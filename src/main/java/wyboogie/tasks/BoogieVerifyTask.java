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

import java.util.Collections;
import java.util.List;

import jbfs.core.Build;
import jbfs.core.Build.Artifact;
import jbfs.core.Build.SnapShot;
import jbfs.util.Pair;
import jbfs.util.Trie;
import wyboogie.core.BoogieFile;
import wyboogie.util.Boogie;
import wycc.lang.SyntacticException;
import wycc.lang.SyntacticItem;
import wyc.util.ErrorMessages;
import wyil.lang.WyilFile;

public class BoogieVerifyTask implements Build.Task {
	/**
	 * Handle for the boogie verifier, making sure to enable the array theory (as
	 * this really helps!)
	 */
	private final Boogie verifier = new Boogie().setArrayTheory();
	/**
	 * The source file that this task will compiler from.
	 */
	private final Trie source;
	/**
	 * Identifier for target of this build task.
	 */
	private final Trie target;
	/**
	 * Specify whether to print verbose progress messages or not
	 */
	private boolean verbose = true;
	/**
	 * Boogie process timeout (in seconds)
	 */
	private int timeout = 10;

	public BoogieVerifyTask(Trie target, Trie source) {
		if(target == null) {
			throw new IllegalArgumentException("invalid target");
		} else if(source == null) {
			throw new IllegalArgumentException("invalid source");
		}
		this.target = target;
		this.source = source;
	}

	public BoogieVerifyTask setVerbose(boolean flag) {
		this.verbose = flag;
		return this;
	}

	public BoogieVerifyTask setTimeout(int timeout) {
		this.timeout = timeout;
		return this;
	}

	@Override
	public Trie getPath() {
		return target;
	}

	@Override
	public Type<? extends Artifact> getContentType() {
		return BoogieFile.ContentType;
	}

	@Override
	public List<? extends Artifact> getSourceArtifacts() {
		return Collections.EMPTY_LIST;
	}

	/**
	 * The business end of a compilation task. The intention is that this
	 * computation can proceed without performing any blocking I/O. This means it
	 * can be used in e.g. a forkjoin task safely.
	 *
	 * @param binary --- The WyilFile being translated.
	 * @return
	 */
	@Override
	public Pair<SnapShot,Boolean> apply(SnapShot snapshot) {
		// Read out WyilFile being translated into Boogie.
		WyilFile binary = snapshot.get(WyilFile.ContentType, source);
		BoogieFile target = snapshot.get(BoogieFile.ContentType, this.target);
		boolean result = true;
		//
		String id = target.getPath().toString();
		Boogie.Message[] errors = verifier.check(timeout * 1000, id, target);
		//
		if(errors == null) {
			// A timeout occurred
			throw new SyntacticException("Boogie timeout after " + timeout + "s", binary, null);
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
					throw new SyntacticException(err.toString(), binary, wyItem);
				}
				}
			}
		}
		result = errors != null && errors.length == 0;
		//
		return new Pair<>(snapshot,result);
	}
}