// Copyright 2020 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wyboogie.tasks;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.function.Function;

import wyboogie.core.BoogieFile;
import wyboogie.util.Boogie;
import wybs.lang.Build;
import wybs.lang.Build.Meter;
import wybs.lang.SyntacticException;
import wybs.lang.SyntacticHeap;
import wybs.lang.SyntacticItem;
import wybs.util.AbstractBuildTask;
import wyc.util.ErrorMessages;
import wyfs.lang.Path;
import wyil.lang.WyilFile;

public class BoogieCompileTask extends AbstractBuildTask<WyilFile, BoogieFile> {
	/**
	 * Handle for the boogie verifier, making sure to enable the array theory (as
	 * this really helps!)
	 */
	private final Boogie verifier = new Boogie().setArrayTheory();
	/**
	 * Specify whether to print verbose progress messages or not
	 */
	private boolean verbose = true;
	/**
	 * Specify debugging mode (this disables mangling, etc)
	 */
	private boolean debug = false;
	/**
	 * Boogie process timeout (in seconds)
	 */
	private int timeout = 10;
	/**
	 * Determines whether or not to verify generate files with Boogie.
	 */
	private boolean verification = false;

	public BoogieCompileTask(Build.Project project, Path.Entry<BoogieFile> target, Path.Entry<WyilFile> source) {
		super(project, target, Arrays.asList(source));
	}

	public void setVerification(boolean flag) {
		this.verification = flag;
	}

	public void setVerbose(boolean flag) {
		this.verbose = flag;
	}

	public void setDebug(boolean flag) {
		this.debug = flag;
	}


	public void setTimeout(int timeout) {
		this.timeout = timeout;
	}

	@Override
	public Function<Meter,Boolean> initialise() throws IOException {
		// Extract target and source files for compilation. This is the component which
		// requires I/O.
		BoogieFile bf = target.read();
		WyilFile wyf = sources.get(0).read();
		// Construct the lambda for subsequent execution. This will eventually make its
		// way into some kind of execution pool, possibly for concurrent execution with
		// other tasks.
		return (Meter meter) -> execute(meter, bf, wyf);
	}

	/**
	 * The business end of a compilation task. The intention is that this
	 * computation can proceed without performing any blocking I/O. This means it
	 * can be used in e.g. a forkjoin task safely.
	 *
	 * @param target  --- The Boogie being written.
	 * @param sources --- The WyilFile(s) being translated.
	 * @return
	 */
	public boolean execute(Build.Meter meter, BoogieFile target, WyilFile source) {
		meter = meter.fork("BoogieCompiler");
		//
		BoogieCompiler bc = new BoogieCompiler(meter,target);
		// Configure debug mode (if applicable)
		bc.setMangling(!debug);
		// Run the translation!
		bc.visitModule(source);
		//
		meter.done();
		//
		if (verification) {
			String id = source.getEntry().id().toString();
			Boogie.Message[] errors = verifier.check(timeout * 1000, id, target);
			//
			if(errors == null) {
				// A timeout occurred
				throw new SyntacticException("Boogie timeout after " + timeout + "s", source.getEntry(), null);
			} else if(verbose && errors.length > 0) {
				System.out.println("=================================================");
				System.out.println("Errors: " + id);
				System.out.println("=================================================");
				for(int i=0;i!=errors.length;++i) {
					System.out.println(errors[i]);
				}
			}
			// Apply errors
			for (int i = 0; i != errors.length; ++i) {
				Boogie.Message ith = errors[i];
				if (ith instanceof Boogie.Error) {
					Boogie.Error err = (Boogie.Error) ith;
					BoogieFile.Item item = err.getEnclosingItem();
					// Attempt to extract corresponding syntactic item (if any)
					SyntacticItem wyItem = item.getAttribute(SyntacticItem.class);
					// Attempt to extract error code (if any)
					Integer errcode = item.getAttribute(Integer.class);
					//
					switch (err.getCode()) {
						case Boogie.ERROR_ASSERTION_FAILURE: {
							BoogieFile.Stmt.Assert stmt = (BoogieFile.Stmt.Assert) item;
							// Update item since the assertion is not our objective!
							wyItem = stmt.getCondition().getAttribute(SyntacticItem.class);
							// NOTE: since a lot of Whiley failures are encoded as Boogie asserts, we must decode the exact kind of failure.
							ErrorMessages.syntaxError(wyItem, errcode);
							break;
						}
						case Boogie.ERROR_PRECONDITION_FAILURE: {
							ErrorMessages.syntaxError(wyItem, WyilFile.STATIC_PRECONDITION_FAILURE);
							break;
						}
						case Boogie.ERROR_POSTCONDITION_FAILURE: {
							ErrorMessages.syntaxError(wyItem, WyilFile.STATIC_POSTCONDITION_FAILURE);
							break;
						}
						case Boogie.ERROR_ESTABLISH_LOOP_INVARIANT_FAILURE: {
							ErrorMessages.syntaxError(wyItem, WyilFile.STATIC_ENTER_LOOPINVARIANT_FAILURE);
							break;
						}
						case Boogie.ERROR_RESTORE_LOOP_INVARIANT_FAILURE: {
							ErrorMessages.syntaxError(wyItem, WyilFile.STATIC_RESTORE_LOOPINVARIANT_FAILURE);
							break;
						}
						default: {
							// Fall back
							throw new SyntacticException(err.toString(), source.getEntry(), wyItem);
						}
					}
				}
			}
			return errors != null && errors.length == 0;
		}
		//
		return true;
	}

}
