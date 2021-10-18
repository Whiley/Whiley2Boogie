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

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import jbfs.core.Build;
import jbfs.core.Content;
import jbfs.util.ByteRepository;
import jbfs.util.DirectoryRoot;
import jbfs.util.Pair;
import jbfs.util.Transactions;
import jbfs.util.Trie;
import wyboogie.core.BoogieFile;
import wyboogie.tasks.BoogieBuildTask;
import wyboogie.tasks.BoogieVerifyTask;
import wycc.lang.SyntacticException;

import wyc.lang.WhileyFile;
import wyc.task.CompileTask;
import wyc.util.TestUtils;
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
public class WhileyCompilerTests {
	public enum Error {
		OK, // Test compiled and verified correctly
		FAILED_COMPILE, // Test did not compile
		FAILED_VERIFY, // Test failed boogie
		EXCEPTION,	// internal failure
	}
	/**
	 * Configure Timeout to use for Boogie (in seconds)
	 */
	public final static int TIMEOUT = 60;
	/**
	 * Configure debug mode which (when enabled) produces easier to read Boogie output.  This should not be enabled by default.
	 */
	private final static boolean DEBUG = false;
	/**
	 * The directory containing the valid source files for each test case. Every test
	 * corresponds to a file in this directory.
	 */
	public final static java.nio.file.Path VALID_SRC_DIR = Paths.get("tests/valid");
	/**
	 * The directory containing the invalid source files for each test case. Every test
	 * corresponds to a file in this directory.
	 */
	public final static java.nio.file.Path INVALID_SRC_DIR = Paths.get("tests/invalid");

	/**
	 * Ignored tests and a reason why we ignore them.
	 */
	private final static Map<String, String> IGNORED= new HashMap<>();

	static {
		// ===================================================
		// WyC problems
		// ===================================================
		// Bring over all the currently failing tests for the compiler. There's
		// absolutely no point trying to see whether these work or not, since we
		// already know they will not.
		IGNORED.putAll(TestUtils.VALID_IGNORED);

		// ==========================================================
		// Valid Tests
		// ==========================================================

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
		IGNORED.put("Lambda_Valid_30","#123");
		IGNORED.put("Process_Valid_9","#56");
		IGNORED.put("Process_Valid_10","#56");
		IGNORED.put("Property_Valid_17","#55");
		IGNORED.put("RecursiveType_Valid_7","#98");
		IGNORED.put("RecursiveType_Valid_19","#79");
		IGNORED.put("RecursiveType_Valid_20","#79");
		IGNORED.put("Requires_Valid_2","#79");
		IGNORED.put("Reference_Valid_6","#56");
		IGNORED.put("Reference_Valid_11","#61");
		IGNORED.put("Reference_Valid_24","#89");
		IGNORED.put("Unsafe_Valid_4","#112");
		IGNORED.put("Unsafe_Valid_5","#112");
		IGNORED.put("Reference_Valid_39","#115");
		// Old stuff
		IGNORED.put("Reference_Valid_23","#127");
		IGNORED.put("Reference_Valid_29","#127");
		IGNORED.put("Reference_Valid_33","#127");
		IGNORED.put("Old_Valid_9","#128");
		IGNORED.put("Old_Valid_10","#128");
		IGNORED.put("Old_Valid_11","#127");
		IGNORED.put("Old_Valid_12","#127");
		IGNORED.put("Old_Valid_17","#128");
		IGNORED.put("Old_Valid_18","#128");
		IGNORED.put("Old_Valid_19","#127");
		IGNORED.put("Old_Valid_20","#127");
		IGNORED.put("Old_Valid_21","#127");
		IGNORED.put("Old_Valid_22","#127");
		// ==========================================================
		// Invalid Tests
		// ==========================================================
		IGNORED.put("Parsing_Invalid_1", "608");
		IGNORED.put("Parsing_Invalid_2", "608");
		// #885 --- Contractive Types and isVoid()
		IGNORED.put("Type_Invalid_5", "885");
		IGNORED.put("Type_Invalid_7", "??");
		IGNORED.put("Type_Invalid_8", "??");
		// Access Static Variable from Type Invariant
		IGNORED.put("Type_Invalid_11", "793");
		IGNORED.put("Reference_Invalid_2", "unclassified");
		IGNORED.put("While_Invalid_25", "#956");
	}

	// ======================================================================
	// Test Harness
	// ======================================================================

	@Test
	public void debug() throws IOException {
//	     For when you want to debug a specific test case.
		testValid("Test_Valid_1");
	}

	@ParameterizedTest
	@MethodSource("validSourceFiles")
 	public void testValid(String name) throws IOException {
		// Compile to Java Bytecode
		Pair<Error, String> p = compileWhiley2Boogie(VALID_SRC_DIR, // location of source directory
				name); // name of test to compile
		// Check outcome was positive
		if (p.first() != Error.OK) {
			System.err.println(p.second());
			fail("Test failed to compile!");
		}
	}

	@ParameterizedTest
	@MethodSource("invalidSourceFiles")
	public void testInvalid(String name) throws IOException {
		File whileySrcDir = INVALID_SRC_DIR.toFile();
		// Compile to Java Bytecode
		Pair<Error, String> p = compileWhiley2Boogie(INVALID_SRC_DIR, // location of source directory
				name); // name of test to compile
		// Check outcome was negative
		if(p.first() == Error.FAILED_COMPILE) {
			// Ignore tests which fail because they cannot be compiled by the Whiley
			// Compiler. We're only interested in tests which pass through to verification.
		} else if (p.first() != Error.FAILED_VERIFY) {
			fail("Test should have failed to compile / verify!");
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
	public static Pair<Error,String> compileWhiley2Boogie(java.nio.file.Path whileydir, String arg) throws IOException {
		String filename = arg + ".whiley";
		ByteArrayOutputStream syserr = new ByteArrayOutputStream();
		PrintStream psyserr = new PrintStream(syserr);
		// Determine the ID of the test being compiler
		Trie path = Trie.fromString(arg);
		//
		Error result;
		// Construct the directory root
		DirectoryRoot root = new DirectoryRoot(registry, whileydir.toFile(), f -> {
			return f.getName().equals(filename);
		});
		// Extract source file
		WhileyFile source = root.get(WhileyFile.ContentType, path);
		// Construct build repository
		Build.Repository repository = new ByteRepository(registry, source);
		//
		try {
			// Apply Whiley Compiler to repository
			if(repository.apply(Transactions.create(new CompileTask(path, source)))) {
				WyilFile target = repository.get(WyilFile.ContentType, path);
				root.put(path, target);
				BoogieBuildTask bt = new BoogieBuildTask(path, path).setDebug(DEBUG);
				if(repository.apply(Transactions.create(bt))) {
					BoogieFile boogie = repository.get(BoogieFile.ContentType, path);
					root.put(path, boogie);
					if(repository.apply(Transactions.create(new BoogieVerifyTask(path, path)))) {
						result = Error.OK;
					} else {
	 					result = Error.FAILED_VERIFY;
	 				}
 				} else {
 					throw new IllegalArgumentException("deadcode");
 				}
				// Print out syntactic markers
				wycli.commands.BuildCmd.printSyntacticMarkers(psyserr, target, source);
			} else {
				result = Error.FAILED_COMPILE;
			}
		} catch (SyntacticException e) {
			// Print out the syntax error
			e.outputSourceError(psyserr);
			result = Error.EXCEPTION;
		} catch (Exception e) {
			// Print out the syntax error
			wyc.util.TestUtils.printStackTrace(psyserr, e);
			result = Error.EXCEPTION;
		} finally {
			// Writeback any results
			root.synchronise();
		}
		//
		psyserr.flush();
		// Convert bytes produced into resulting string.
		byte[] errBytes = syserr.toByteArray();
		String output = new String(errBytes);
		return new Pair<>(result, output);
	}

	// ======================================================================
	// Data sources
	// ======================================================================

	// Here we enumerate all available test cases.
	private static Stream<String> validSourceFiles() throws IOException {
		return readTestFiles(VALID_SRC_DIR, f -> notIgnored(f));
	}
	private static Stream<String> invalidSourceFiles() throws IOException {
		return readTestFiles(INVALID_SRC_DIR, f -> notIgnored(f));
	}
	public static Stream<String> readTestFiles(java.nio.file.Path dir, Predicate<java.nio.file.Path> filter) throws IOException {
		ArrayList<String> testcases = new ArrayList<>();
		//
		Files.walk(dir,1).forEach(f -> {
			if (f.toString().endsWith(".whiley") && filter.test(f)) {
				// Determine the test name
				testcases.add(extractTestName(f));
			}
		});
		// Sort the result by filename
		Collections.sort(testcases);
		//
		return testcases.stream();
	}

	public static boolean notIgnored(java.nio.file.Path f) {
		return !IGNORED.containsKey(extractTestName(f));
	}

	private static String extractTestName(java.nio.file.Path f) {
		return f.getFileName().toString().replace(".whiley","");
	}
}
