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
package wyboogie;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import wyboogie.core.BoogieFile;
import wyboogie.io.BoogieFilePrinter;
import wyboogie.tasks.BoogieBuildTask;
import wycc.util.Logger;
import wycc.util.MailBox;
import wycc.util.OptArg;
import wycc.util.Trie;
import wyil.lang.WyilFile;
import wyil.lang.WyilFile.Attr.SyntaxError;

public class Main {
	private final BoogieBuildTask task = new BoogieBuildTask(Logger.NULL);
	/**
	 * The outgoing mailbox for this compiler. Essentially, all generated syntax
	 * errors are sent here.
	 */
	private MailBox<SyntaxError> mailbox = new wyc.Compiler.PrintStreamErrorHandler(System.out);
	/**
	 * The output stream from this compiler.
	 */
	private PrintStream out = System.out;
	/**
	 * Destination directory of Wyil files.
	 */
	private File wyildir = new File(".");
	/**
	 * Destination directory of Wyil files.
	 */
	private File bpldir = new File(".");
	/**
	 * List of source files.
	 */
	private List<Trie> sources = new ArrayList<>();
	/**
	 * Determine target filename.
	 */
	private Trie target = Trie.fromString("main");
	/**
	 * WyIL dependencies to include during compilation.
	 */
	private List<File> whileypath = Collections.EMPTY_LIST;

	public Main setErrorHandler(MailBox<SyntaxError> mailbox) {
		this.mailbox = mailbox;
		return this;
	}

	public Main addSource(Trie source) {
		this.sources.add(source);
		return this;
	}

	public Main setTarget(Trie target) {
		this.target = target;
		return this;
	}

	public Main setWyilDir(File wyildir) {
		this.wyildir = wyildir;
		return this;
	}

	public Main setBplDir(File bpldir) {
		this.bpldir = bpldir;
		return this;
	}

	public Main setWhileyPath(List<File> whileypath) {
		this.whileypath = whileypath;
		return this;
	}

	public Main setVerbose(boolean flag) {
		this.task.setVerbose(flag);
		if(flag) {
			this.task.setLogger(new Logger.Default(out));
		}
		return this;
	}

	public Main setVerify(boolean flag) {
		this.task.setVerify(flag);
		return this;
	}

	public Main setDebug(boolean flag) {
		this.task.setDebug(flag);
		return this;
	}

	public Main setTimeout(int n) {
		this.task.setTimeout(n);
		return this;
	}

	public Main setBoogieOption(String key, boolean flag) {
		task.setBoogieOption(key, flag);
		return this;
	}

	public Main setBoogieOption(String key, int n) {
		task.setBoogieOption(key, n);
		return this;
	}

	public Main setBoogieOption(String key, String s) {
		task.setBoogieOption(key, s);
		return this;
	}

	public boolean run() throws IOException {
		// Add sources
		for(Trie source : sources) {
			// Extract source file
			task.addSource(wyc.Compiler.readWyilFile(wyildir, source));
		}
		// Extract any dependencies from zips
		for(File dep : whileypath) {
			List<WyilFile> deps = new ArrayList<>();
			wyc.Compiler.extractDependencies(dep,deps);
			task.addSources(deps);
		}
		// Run the compiler
		BoogieFile target = task.run();
		boolean valid = true;
		// Write out syntactic markers
		for(WyilFile binary : task.getSources()) {
			valid &= binary.isValid();
			wyc.Compiler.writeSyntacticMarkers(mailbox,binary);
		}
		// Write out binary target
		writeBoogieFile(this.target, target, bpldir);
		//
		return valid;
	}

	/**
	 * Command-line options
	 */
	private static final OptArg[] OPTIONS = {
			// Standard options
			new OptArg("verbose","v","set verbose output"),
			new OptArg("debug","d","set debug mode"),
			new OptArg("timeout", "t", OptArg.INT, "set boogie timeout (s)", 10),
			new OptArg("noverify","v","don't verify generated Boogie"),
			new OptArg("output","o",OptArg.STRING,"set output file","main"),
			new OptArg("wyildir", OptArg.FILEDIR, "Specify where to place binary (WyIL) files", new File(".")),
			new OptArg("bpldir", OptArg.FILEDIR, "Specify where to place Boogie files", new File(".")),
			new OptArg("whileypath", OptArg.FILELIST, "Specify additional dependencies", new ArrayList<>()),
			new OptArg("useArrayTheory","u","use Boogie array theory"),
			new OptArg("proverLog", OptArg.FILE, "Specify log file for theorem prover"),
			new OptArg("proverName", OptArg.FILE, "Specify name of theorem prover (e.g. z3, cvc5, etc)")
	};

	public static void main(String[] _args) throws IOException {
		List<String> args = new ArrayList<>(Arrays.asList(_args));
		Map<String, Object> options = OptArg.parseOptions(args, OPTIONS);
		//
		boolean verbose = options.containsKey("verbose");
		Trie target = Trie.fromString((String) options.get("output"));
		File wyildir = (File) options.get("wyildir");
		File bpldir = (File) options.get("bpldir");
		ArrayList<File> whileypath = (ArrayList<File>) options.get("whileypath");
		boolean debug = options.containsKey("debug");
		boolean verify = !options.containsKey("noverify");
		int timeout = (Integer) options.get("timeout");
		boolean useArrayTheory = options.containsKey("useArrayTheory");
		// Construct Main object
		Main main = new Main().setVerbose(verbose).setWyilDir(wyildir).setBplDir(bpldir).setTarget(target)
				.setWhileyPath(whileypath).setDebug(debug).setTimeout(timeout).setVerify(verify)
				.setBoogieOption("useArrayTheory", useArrayTheory);
		// Configure prover log (if requested)
		if(options.containsKey("proverLog")) {
			main = main.setBoogieOption("proverLog", options.get("proverLog").toString());
		}
		// Configure alternative prover (if requested)
		if(options.containsKey("proverName")) {
			main = main.setBoogieOption("proverOpt", "PROVER_NAME=" + options.get("proverName").toString());
		}
		// Add source files
		for (String s : args) {
			main.addSource(Trie.fromString(s));
		}
		// Run the compiler!
		boolean result = main.run();
		// Produce exit code
		System.exit(result ? 0 : 1);
	}

	/**
	 * Write a given WyilFile to disk using the given directory as a root.
	 *
	 * @param wf
	 * @param dir
	 * @throws IOException
	 */
	public static void writeBoogieFile(Trie target, BoogieFile wf, File dir) throws IOException {
		String filename = target.toNativeString() + ".bpl";
		try (FileOutputStream fout = new FileOutputStream(new File(dir, filename))) {
			new BoogieFilePrinter(fout).write(wf);
			fout.flush();
		}
	}

}
