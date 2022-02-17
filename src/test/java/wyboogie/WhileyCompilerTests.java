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
import java.nio.file.Path;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.fail;

import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import wycc.util.Trie;
import wyc.util.TestUtils;

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
	public final static Path VALID_SRC_DIR = Paths.get("tests/valid");
	/**
	 * The directory containing the invalid source files for each test case. Every test
	 * corresponds to a file in this directory.
	 */
	public final static Path INVALID_SRC_DIR = Paths.get("tests/invalid");

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
		IGNORED.put("Reference_Valid_42","");
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
		// Unsafe
		IGNORED.put("Unsafe_Invalid_4","??");
		IGNORED.put("Unsafe_Invalid_5","??");
		IGNORED.put("Unsafe_Invalid_6","??");
		IGNORED.put("Unsafe_Invalid_7","??");
		IGNORED.put("Unsafe_Invalid_8","??");
		IGNORED.put("Unsafe_Invalid_9","??");
		IGNORED.put("Unsafe_Invalid_10","??");
		IGNORED.put("Unsafe_Invalid_11","??");
		IGNORED.put("Unsafe_Invalid_12","??");

	}

	// ======================================================================
	// Test Harness
	// ======================================================================

	@Disabled
	@Test
	public void debug() throws IOException {
//	     For when you want to debug a specific test case.
		//testValid("Test_Valid_1");
	}

	@ParameterizedTest
	@MethodSource("validSourceFiles")
 	public void testValid(Trie name) throws IOException {
		// Compile to Java Bytecode
		Error e = compileWhiley2Boogie(VALID_SRC_DIR, // location of source directory
				name); // name of test to compile
		// Check outcome was positive
		if (e != Error.OK) {
			fail("Test failed to compile! " + name);
		}
	}

	@ParameterizedTest
	@MethodSource("invalidSourceFiles")
	public void testInvalid(Trie name) throws IOException {
		// Compile to Java Bytecode
		Error e = compileWhiley2Boogie(INVALID_SRC_DIR, // location of source directory
				name); // name of test to compile
		// Check outcome was negative
		if(e == Error.FAILED_COMPILE) {
			// Ignore tests which fail because they cannot be compiled by the Whiley
			// Compiler. We're only interested in tests which pass through to verification.
		} else if (e != Error.FAILED_VERIFY) {
			fail("Test should have failed to compile / verify! " + name);
		}
	}

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
	public static Error compileWhiley2Boogie(Path whileyDir, Trie path) throws IOException {
		File whileySrcDir = whileyDir.toFile();
		// Configure and run Whiley compiler.
		boolean r = new wyc.Compiler().setWhileyDir(whileySrcDir).setWyilDir(whileySrcDir).setTarget(path)
				.addSource(path).run();
		if (!r) {
			return Error.FAILED_COMPILE;
		}
		// Configure and run JavaScript backend.
		r = new Main().setWyilDir(whileySrcDir).setBplDir(whileySrcDir).setTarget(path).addSource(path)
				.setTimeout(TIMEOUT).setBoogieOption("useArrayTheory", true).run();
		if(!r) {
			return Error.FAILED_VERIFY;
		} else {
			//
			return Error.OK;
		}
	}

	// ======================================================================
	// Data sources
	// ======================================================================

	// Here we enumerate all available test cases.
	private static Stream<Trie> validSourceFiles() throws IOException {
		return readTestFiles(VALID_SRC_DIR, f -> notIgnored(f));
	}
	private static Stream<Trie> invalidSourceFiles() throws IOException {
		return readTestFiles(INVALID_SRC_DIR, f -> notIgnored(f));
	}
	public static Stream<Trie> readTestFiles(java.nio.file.Path dir, Predicate<java.nio.file.Path> filter) throws IOException {
		ArrayList<Trie> testcases = new ArrayList<>();
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
		return !IGNORED.containsKey(extractTestName(f).toString());
	}

	private static Trie extractTestName(java.nio.file.Path f) {
		return Trie.fromString(f.getFileName().toString().replace(".whiley",""));
	}
}
