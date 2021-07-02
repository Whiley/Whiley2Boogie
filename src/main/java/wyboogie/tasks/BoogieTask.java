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

import java.util.List;

import wyboogie.core.BoogieFile;
import wyboogie.util.Boogie;
import wycc.lang.Build;
import wycc.lang.Build.SnapShot;
import wycc.lang.Filter;
import wycc.lang.SyntacticException;
import wycc.lang.SyntacticItem;
import wycc.util.Pair;
import wyc.util.ErrorMessages;
import wyil.lang.WyilFile;

public class BoogieTask implements Build.Task {
	private final Build.Meter meter = Build.NULL_METER;
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
	/**
	 * Determine the set of files which will be compiled by this task.
	 */
	private final Filter includes = Filter.fromString("**/*");

	public BoogieTask() {

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
	public Pair<SnapShot, Boolean> apply(SnapShot t) {
		boolean b = true;
		// Identify all Whiley intermediate files
		List<WyilFile> sources = t.match(WyilFile.class, includes);
		//
		for (WyilFile src : sources) {
			BoogieFile bin = new BoogieFile(src.getPath());
			b &= compile(bin, src);
			// Write target into snapshot
			t = t.put(bin);
		}
		// Done
		return new Pair<>(t, b);
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
	public boolean compile(BoogieFile target, WyilFile source) {
		BoogieCompiler bc = new BoogieCompiler(meter,target);
		// Configure debug mode (if applicable)
		bc.setMangling(!debug);
		// Run the translation!
		bc.visitModule(source);
		//
		meter.done();
		//
		if (verification) {
			String id = source.getPath().toString();
			Boogie.Message[] errors = verifier.check(timeout * 1000, id, target);
			//
			if(errors == null) {
				// A timeout occurred
				throw new SyntacticException("Boogie timeout after " + timeout + "s", source, null);
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
					if(wyItem == null && item instanceof BoogieFile.Stmt.Assert) {
						BoogieFile.Stmt.Assert stmt = (BoogieFile.Stmt.Assert) item;
						// Update item since the assertion is not our objective!
						wyItem = stmt.getCondition().getAttribute(SyntacticItem.class);
					}
					//
					switch (err.getCode()) {
						case Boogie.ERROR_ASSERTION_FAILURE: {
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
							throw new SyntacticException(err.toString(), source, wyItem);
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
