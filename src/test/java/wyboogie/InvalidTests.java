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
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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


@RunWith(Parameterized.class)
public class InvalidTests {

	/**
	 * The directory containing the source files for each test case. Every test
	 * corresponds to a file in this directory.
	 */
	public final static String WHILEY_SRC_DIR = "tests/invalid".replace('/', File.separatorChar);

	/**
	 * Ignored tests and a reason why we ignore them.
	 */
	public final static Map<String, String> IGNORED = new HashMap<>();
		static {
			IGNORED.put("Parsing_Invalid_1", "608");
			IGNORED.put("Parsing_Invalid_2", "608");
			// Access Static Variable from Type Invariant
			IGNORED.put("Type_Invalid_11", "793");
			// Problems with counterexample generation?
//			IGNORED.put("DoWhile_Invalid_6", "??");
//			IGNORED.put("DoWhile_Invalid_8", "??");
//			IGNORED.put("While_Invalid_18", "??");
//			IGNORED.put("While_Invalid_20", "??");
//			IGNORED.put("While_Invalid_21", "??");
//			IGNORED.put("While_Invalid_22", "??");
//			IGNORED.put("While_Invalid_23", "??");
//			IGNORED.put("TupleAssign_Invalid_3", "??");
//			IGNORED.put("TypeEquals_Invalid_5", "??");
//		// #885 --- Contractive Types and isVoid()
			IGNORED.put("Type_Invalid_5", "885");
			IGNORED.put("Type_Invalid_8", "??");
			IGNORED.put("Reference_Invalid_2", "unclassified");
			IGNORED.put("Type_Invalid_14", "??");
			IGNORED.put("Type_Invalid_15", "??");
			IGNORED.put("While_Invalid_24", "??");
			IGNORED.put("While_Invalid_25", "#956");
			IGNORED.put("For_Invalid_9", "#982");
			IGNORED.put("Reference_Invalid_5", "??");
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
		System.out.println(p.second());
		if (r) {
			fail("Test should have failed to compile / verify!");
		}
//		String output = p.second();
//
//		// Now, let's check the expected output against the file which
//		// contains the sample output for this test
//		String sampleOutputFile = WHILEY_SRC_DIR + File.separatorChar + name
//				+ ".sysout";
//		// Third, compare the output!
//		if(!TestUtils.compare(output,sampleOutputFile)) {
//			fail("Output does not match reference");
//		}
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
		// Construct the project
		DirectoryRoot root = new DirectoryRoot(whileydir, registry);
		//
		boolean result = true;
		//
		try {
			//
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
			result = true;
		} catch (Exception e) {
			// Print out the syntax error
			e.printStackTrace(new PrintStream(syserr));
			result = true;
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
	public InvalidTests(String testName) {
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
