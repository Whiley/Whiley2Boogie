// Copyright 2011 The Whiley Project Developers
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
package wyboogie.util.testing;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Map;

import wyboogie.Main;
import wycc.lang.Syntactic;
import wycc.util.MailBox;
import wycc.util.TextFile;
import wycc.util.Trie;
import wycc.util.testing.TestFile;
import wycc.util.testing.TestFile.Error;
import wycc.util.testing.TestStage.Result;
import wycc.util.testing.TestStage;
import wyc.util.testing.WhileyCompileTest;
import wyil.lang.WyilFile;
import wyil.lang.WyilFile.Attr.SyntaxError;

public class BoogieVerifyTest implements TestStage {
	private static final int MIN_VERIFICATION_ERROR = 716;
	private static final int MAX_VERIFICATION_ERROR = 731;
	/**
	 * Configure Timeout to use for Boogie (in seconds)
	 */
	private int timeout = 60;
	/**
	 * Configure debug mode which (when enabled) produces easier to read Boogie output.  This should not be enabled by default.
	 */
	private boolean debug = false;
	/**
	 * Configure Boogie to use an alternative SMT solver. This should be
	 * <code>null</code> in the general case, as this signals boogie to use the
	 * default (i.e. Z3). However, for debugging, you can override it.
	 */
	private String proverName = null;

	public BoogieVerifyTest setTimeout(int timeout) {
		this.timeout = timeout;
		return this;
	}

	public BoogieVerifyTest setDebug(boolean flag) {
		this.debug = flag;
		return this;
	}

	public BoogieVerifyTest setProverName(String name) {
		this.proverName = name;
		return this;
	}

	@Override
	public Result apply(Trie path, Path dir, Map<Trie, TextFile> state, TestFile tf) throws IOException {
		boolean ignored = tf.get(Boolean.class, "boogie.ignore").orElse(false);
		String unit = tf.get(String.class, "main.file").orElse("main");
		int timeout = tf.get(Integer.class, "boogie.timeout").orElse(this.timeout);
		//
		MailBox.Buffered<SyntaxError> handler = new MailBox.Buffered<>();
		try {
			// Configure and run JavaScript backend.
			Main m = new Main().setWyilDir(dir.toFile()).setBplDir(dir.toFile()).setTarget(path).addSource(path)
					.setTimeout(timeout).setBoogieOption("useArrayTheory", true).setDebug(debug).setVerbose(debug)
					.setErrorHandler(handler);
			if (proverName != null) {
				m.setBoogieOption("proverOpt", "PROVER_NAME=" + proverName);
			}
			boolean r = m.run();
			// Done
			TestFile.Error[] markers = handler.stream().map(se -> WhileyCompileTest.toError(state, se))
					.toArray(TestFile.Error[]::new);
			//
			return new TestStage.Result(ignored, markers);
		} catch (Syntactic.Exception e) {
			e.printStackTrace();
			if(e.getElement() != null) {
				TestFile.Error err = WhileyCompileTest.toError(state,e);
				return new TestStage.Result(ignored,new TestFile.Error[] {err});
			} else {
				TestFile.Coordinate c = new TestFile.Coordinate(0, new TestFile.Range(0, 0));
				return new Result(ignored, new Error(WyilFile.INTERNAL_FAILURE, Trie.fromString(unit), c));
			}
		} catch(Throwable e) {
			e.printStackTrace();
			TestFile.Coordinate c = new TestFile.Coordinate(0, new TestFile.Range(0, 0));
			return new Result(ignored, new Error(WyilFile.INTERNAL_FAILURE, Trie.fromString(unit), c));
		}
	}

	@Override
	public Error[] filter(Error[] errors) {
		return Arrays.asList(errors).stream().filter(m -> isVerificationError(m.getErrorNumber()))
				.toArray(TestFile.Error[]::new);
	}

	public static boolean isVerificationError(int m) {
		return MIN_VERIFICATION_ERROR <= m && m <= MAX_VERIFICATION_ERROR;
	}


}
