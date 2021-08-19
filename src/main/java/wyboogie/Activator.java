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
package wyboogie;

import wycc.lang.Build;
import wycc.lang.Filter;
import wycc.util.AbstractCompilationUnit.Value;
import wycli.cfg.Configuration;
import wycli.lang.Command;
import wycli.lang.Plugin;
import wycc.lang.Content;
import wycc.lang.Path;
import wyil.lang.WyilFile;

import java.io.IOException;
import java.math.BigInteger;
import java.util.List;

import wyboogie.core.BoogieFile;
import wyboogie.tasks.BoogieTask;

public class Activator implements Plugin.Activator {

	public static Path PACKAGE_NAME = Path.fromString("package/name");
	public static Path BUILD_WHILEY_TARGET = Path.fromString("build/whiley/target");
	public static Path BUILD_BOOGIE_TARGET = Path.fromString("build/boogie/target");
	public static Path BUILD_BOOGIE_VERIFY = Path.fromString("build/boogie/verify");
	public static Path BUILD_BOOGIE_VERBOSE = Path.fromString("build/boogie/verbose");
	public static Path BUILD_BOOGIE_DEBUG = Path.fromString("build/boogie/debug");
	public static Path BUILD_BOOGIE_TIMEOUT = Path.fromString("build/boogie/timeout");
	private static Value.UTF8 TARGET_DEFAULT = new Value.UTF8("bin".getBytes());

	public static Command.Platform BOOGIE_PLATFORM = new Command.Platform() {
		//
		@Override
		public String getName() {
			return "boogie";
		}

		@Override
		public Configuration.Schema getConfigurationSchema() {
			return Configuration.fromArray(
					Configuration.UNBOUND_STRING(BUILD_BOOGIE_TARGET, "Specify location for generated Boogie .bpl files", TARGET_DEFAULT),
					Configuration.UNBOUND_BOOLEAN(BUILD_BOOGIE_VERIFY, "Enable verification of Whiley files using Boogie", new Value.Bool(true)),
					Configuration.UNBOUND_BOOLEAN(BUILD_BOOGIE_VERBOSE, "Enable verbose output", new Value.Bool(false)),
					Configuration.UNBOUND_BOOLEAN(BUILD_BOOGIE_DEBUG, "Enable debug mode", new Value.Bool(false)),
					Configuration.UNBOUND_INTEGER(BUILD_BOOGIE_TIMEOUT, "Set timeout limit (s)", new Value.Int(10))
			);
		}

		@Override
		public Build.Task initialise(Path path, Command.Environment environment) throws IOException {
			// Determine local configuration
			Configuration config = environment.get(path);
			// Determine enclosing package name
			Path pkg = Path.fromString(config.get(Value.UTF8.class, PACKAGE_NAME).unwrap());
			// Identify directory where generated Boogie files are dumped.
			Path source = Path.fromString(config.get(Value.UTF8.class, BUILD_WHILEY_TARGET).unwrap());
			// Specify directory where generated Boogie files are dumped.
			Path target= Path.fromString(config.get(Value.UTF8.class, BUILD_BOOGIE_TARGET).unwrap());
			// Determine whether verification enabled or not
			boolean verification = config.get(Value.Bool.class, BUILD_BOOGIE_VERIFY).unwrap();
			// Determine whether verbose output enabled or not
			boolean verbose = config.get(Value.Bool.class, BUILD_BOOGIE_VERBOSE).unwrap();
			// Determine whether debug mode enabled or not
			boolean debug = config.get(Value.Bool.class, BUILD_BOOGIE_DEBUG).unwrap();
			// Determine timeout to use
			BigInteger timeout = config.get(Value.Int.class, BUILD_BOOGIE_TIMEOUT).unwrap();
			// Register build target for this package
			return new BoogieTask(target.append(pkg), source.append(pkg)).setVerbose(verbose).setVerification(verification)
					.setDebug(debug).setTimeout(timeout.intValue());
		}
	};

	// =======================================================================
	// Start
	// =======================================================================

	@Override
	public Plugin start(Plugin.Context context) {
		// Register platform
		context.register(Command.Platform.class, BOOGIE_PLATFORM);
		// List of content types
		context.register(Content.Type.class, BoogieFile.ContentType);
		// Done
		return new Plugin() {
			// what goes here?
		};
	}

	// =======================================================================
	// Stop
	// =======================================================================

	@Override
	public void stop(Plugin module, Plugin.Context context) {
		// could do more here?
	}
}
