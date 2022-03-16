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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import wyil.lang.WyilFile;
import wyboogie.core.BoogieFile;
import wyboogie.util.Boogie;
import wyc.util.ErrorMessages;
import wycc.lang.Syntactic;
import wycc.util.Logger;
import wycc.util.Trie;

public class BoogieBuildTask {
	/**
	 * Handle for the boogie verifier.
	 */
	private final Boogie verifier;
	/**
	 * Identifier for target of this build task.
	 */
	private Trie target = Trie.fromString("main");
	/**
	 * The set of source files that this task will compiler from.
	 */
	private final List<WyilFile> sources = new ArrayList<>();
	/**
	 * Specify debugging mode (this disables mangling, etc)
	 */
	private boolean debug = false;
	/**
	 * Specify whether to print verbose progress messages or not
	 */
	private boolean verbose = false;
	/**
	 * Specify whether to enable actual verification or not.
	 */
	private boolean verify = true;
	/**
	 * Boogie process timeout (in seconds)
	 */
	private int timeout = 10;

	public BoogieBuildTask(Logger logger) {
		this.verifier = new Boogie(logger);
	}

	public BoogieBuildTask setDebug(boolean flag) {
		this.debug = flag;
		return this;
	}

	public BoogieBuildTask setVerify(boolean flag) {
		this.verify = flag;
		return this;
	}

	public BoogieBuildTask setLogger(Logger logger) {
		this.verifier.setLogger(logger);
		return this;
	}

	public BoogieBuildTask setTarget(Trie target) {
		this.target = target;
		return this;
	}

	public BoogieBuildTask addSource(WyilFile f) {
		this.sources.add(f);
		return this;
	}

	public BoogieBuildTask addSources(Collection<WyilFile> fs) {
		this.sources.addAll(fs);
		return this;
	}

	public List<WyilFile> getSources() {
		return this.sources;
	}

	public BoogieBuildTask setVerbose(boolean flag) {
		this.verbose = flag;
		return this;
	}

	public BoogieBuildTask setTimeout(int timeout) {
		this.timeout = timeout;
		return this;
	}

	public BoogieBuildTask setBoogieOption(String key, boolean flag) {
		verifier.setBoogieOption(key, flag);
		return this;
	}

	public BoogieBuildTask setBoogieOption(String key, int n) {
		verifier.setBoogieOption(key, n);
		return this;
	}

	public BoogieBuildTask setBoogieOption(String key, String s) {
		verifier.setBoogieOption(key, s);
		return this;
	}

	public BoogieFile run() {
		// Construct initial (empty) Boogie file
		BoogieFile target = new BoogieFile();
		// Process source files one by one
		for (WyilFile i : sources) {
			BoogieCompiler bc = new BoogieCompiler(target);
			// Configure debug mode (if applicable)
			bc.setMangling(!debug);
			// Run the translation!
			bc.visitModule(i);
		}
		// Verify the target (if applicable)
		if(verify) {
			verify(target);
		}
		//
		return target;
	}

	private boolean verify(BoogieFile target) {
		Boogie.Message[] errors = verifier.check(timeout * 1000, this.target.toString(), target);
		//
		if(errors == null) {
			// A timeout occurred
			throw new Syntactic.Exception("Boogie timeout after " + timeout + "s", null, null);
		} else if(verbose && errors.length > 0) {
			System.out.println("=================================================");
			System.out.println("Errors: " + this.target);
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
				Syntactic.Item wyItem = item.getAttribute(Syntactic.Item.class);
				// Attempt to extract error code (if any)
				Integer errcode = item.getAttribute(Integer.class);
				//
				if(wyItem == null && item instanceof BoogieFile.Stmt.Assert) {
					BoogieFile.Stmt.Assert stmt = (BoogieFile.Stmt.Assert) item;
					// Update item since the assertion is not our objective!
					wyItem = stmt.getCondition().getAttribute(Syntactic.Item.class);
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
					throw new Syntactic.Exception(err.toString(), wyItem.getHeap(), wyItem);
				}
				}
			}
		}
		return errors != null && errors.length == 0;
	}
}
