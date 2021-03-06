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

import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.*;
import java.util.concurrent.ForkJoinPool;

import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import wyboogie.core.BoogieFile;
import wyboogie.tasks.BoogieCompileTask;
import wybs.lang.Build;
import wybs.lang.SyntacticException;
import wybs.util.Logger;
import wybs.util.SequentialBuildProject;

import wyc.lang.WhileyFile;
import wyc.task.CompileTask;
import wyc.util.TestUtils;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;
import wyfs.util.Pair;
import wyil.lang.WyilFile;

/**
 * Run through all valid test cases with verification enabled. Since every test
 * file is valid, a successful test occurs when the compiler succeeds and, when
 * executed, the compiled file produces the expected output. Note that an
 * internal failure does not count as a valid pass, and indicates the test
 * exposed some kind of compiler bug.
 *
 * @author David J. Pearce
 *
 */
@RunWith(Parameterized.class)
public class ValidTests {
	/**
	 * Configure Timeout to use for Boogie (in seconds)
	 */
	public final static int TIMEOUT = 60;
	/**
	 * Configure debug mode which (when enabled) produces easier to read Boogie output.  This should not be enabled by default.
	 */
	private final static boolean DEBUG = false;
	/**
	 * The directory containing the source files for each test case. Every test
	 * corresponds to a file in this directory.
	 */
	public final static String WHILEY_SRC_DIR = "tests/valid".replace('/', File.separatorChar);

	/**
	 * Ignored tests and a reason why we ignore them.
	 */
	public final static Map<String, String> IGNORED = new HashMap<>();

	static {
		// ===================================================
		// WyC problems
		// ===================================================
		// Bring over all the currently failing tests for the compiler. There's
		// absolutely no point trying to see whether these work or not, since we
		// already know they will not.
		IGNORED.putAll(TestUtils.VALID_IGNORED);

		// ===================================================
		// Boogie problems
		// ===================================================

		// Not verifiable yet!  These are incomplete in some way which means they could not be verified.
		IGNORED.put("Property_Valid_14","");
		IGNORED.put("Property_Valid_16","");
		IGNORED.put("While_Valid_71","");
		IGNORED.put("Reference_Valid_25",""); // needs old syntax
		IGNORED.put("Reference_Valid_26",""); // needs old syntax
		IGNORED.put("Reference_Valid_30",""); // needs old syntax
		IGNORED.put("Reference_Valid_31",""); // needs old syntax
		// Known issues.  These are known problems with issues raised on github.
		IGNORED.put("ConstrainedList_Valid_18","#26");
		IGNORED.put("Lambda_Valid_13","#52");
		IGNORED.put("Lambda_Valid_24","#59");
		IGNORED.put("Lambda_Valid_25","#59");
		IGNORED.put("Lambda_Valid_26","#52");
		IGNORED.put("Process_Valid_9","#56");
		IGNORED.put("Process_Valid_10","#56");
		IGNORED.put("Property_Valid_17","#55");
		IGNORED.put("RecursiveType_Valid_7","#98");
		IGNORED.put("RecursiveType_Valid_19","#79");
		IGNORED.put("RecursiveType_Valid_20","#79");
		IGNORED.put("Requires_Valid_2","#79");
		IGNORED.put("Reference_Valid_6","#56");
		IGNORED.put("Reference_Valid_11","#61");
		IGNORED.put("Reference_Valid_23","#60");
		IGNORED.put("Reference_Valid_24","#89");
		IGNORED.put("Reference_Valid_29","#60");
		IGNORED.put("Reference_Valid_33","#60");
		IGNORED.put("Reference_Valid_39","#115");
	}

	// ======================================================================
	// Test Harness
	// ======================================================================

 	protected void runTest(String name) throws IOException {
		// Compile to Java Bytecode
		Pair<Boolean, String> p = compileWhiley2Boogie(
				WHILEY_SRC_DIR, // location of source directory
				name); // name of test to compile

		boolean r = p.first();

		if (!r) {
			System.out.println(p.second());
			fail("Test failed to compile!");
		}
	}

 	/**
 	 * A simple default registry which knows about whiley files and wyil files.
 	 */
 	private static final Content.Registry registry = new TestUtils.Registry();

 	/**
	 * Run the Whiley Compiler with the given list of arguments to produce a
	 * Boogie source file. This will then need to be checked separately.
	 *
	 * @param arg
	 *            --- list of command-line arguments to provide to the Whiley
	 *            Compiler.
	 * @return
	 * @throws IOException
	 */
	public static Pair<Boolean,String> compileWhiley2Boogie(String whileydir, String arg) throws IOException {
		ByteArrayOutputStream syserr = new ByteArrayOutputStream();
		ByteArrayOutputStream sysout = new ByteArrayOutputStream();
		PrintStream psyserr = new PrintStream(syserr);
		//
		boolean result = true;
		// Construct the project
		DirectoryRoot root = new DirectoryRoot(whileydir, registry);
		//
		try {
			SequentialBuildProject project = new SequentialBuildProject(root);
			// Identify source files and target files
			Pair<Path.Entry<WhileyFile>,Path.Entry<WyilFile>> p = TestUtils.findSourceFiles(root,arg);
			List<Path.Entry<WhileyFile>> sources = Arrays.asList(p.first());
			Path.Entry<WyilFile> wyilTarget = p.second();
			// Add Whiley => WyIL build rule
			project.add(new Build.Rule() {
				@Override
				public void apply(Collection<Build.Task> tasks) throws IOException {
					// Construct a new build task
					CompileTask task = new CompileTask(project, Logger.NULL, root, wyilTarget, sources);
					// Submit the task for execution
					tasks.add(task);
				}
			});
			// Construct an empty BoogieFile
			Path.Entry<BoogieFile> bgTarget = root.create(wyilTarget.id(), BoogieFile.ContentType);
			BoogieFile bgFile = new BoogieFile();
			// Write out the Boogie file
			bgTarget.write(bgFile);
			// Add WyIL => Boogie Build Rule
			project.add(new Build.Rule() {
				@Override
				public void apply(Collection<Build.Task> tasks) throws IOException {
					// Construct a new build task
					BoogieCompileTask task = new BoogieCompileTask(project, bgTarget, wyilTarget);
					// Set longer timeout
					task.setTimeout(TIMEOUT);
					// Set debug mode
					task.setDebug(DEBUG);
					// Enable verification!
					task.setVerification(true);
					// Submit the task for execution
					tasks.add(task);
				}
			});
			project.refresh();
			// Actually force the project to build
			result = project.build(ForkJoinPool.commonPool(), Build.NULL_METER).get();
			// Check whether any syntax error produced
			result = !TestUtils.findSyntaxErrors(wyilTarget.read().getRootItem(), new BitSet());
			// Print out any error messages
			wycli.commands.Build.printSyntacticMarkers(psyserr, (List) sources, (Path.Entry) wyilTarget);
		} catch (SyntacticException e) {
			// Print out the syntax error
			e.outputSourceError(new PrintStream(syserr),false);
			result = false;
		} catch (Exception e) {
			// Print out the syntax error
			e.printStackTrace(new PrintStream(syserr));
			result = false;
		} finally {
			root.flush();
		}
		// Convert bytes produced into resulting string.
		byte[] errBytes = syserr.toByteArray();
		byte[] outBytes = sysout.toByteArray();
		String output = new String(errBytes) + new String(outBytes);
		return new Pair<>(result, output);
	}

	// ======================================================================
	// Tests
	// ======================================================================

	// Parameter to test case is the name of the current test.
	// It will be passed to the constructor by JUnit.
	private final String testName;
	public ValidTests(String testName) {
		this.testName = testName;
	}

	// Here we enumerate all available test cases.
	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return TestUtils.findTestNames(WHILEY_SRC_DIR);
	}

	// Skip ignored tests
	@Before
	public void beforeMethod() {
		String ignored = IGNORED.get(this.testName);
		Assume.assumeTrue("Test " + this.testName + " skipped: " + ignored, ignored == null);
	}

	@Test
	public void valid() throws IOException {
		if (new File("../../running_on_travis").exists()) {
			System.out.println(".");
		}
		runTest(this.testName);
	}
}
