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

import wybs.lang.Build;
import wybs.util.AbstractBuildRule;
import wybs.util.AbstractCompilationUnit.Value;
import wycli.cfg.Configuration;
import wycli.lang.Command;
import wycli.lang.Module;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.Trie;
import wyil.lang.WyilFile;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;
import java.util.List;

import wyboogie.core.BoogieFile;
import wyboogie.tasks.BoogieCompileTask;

public class Activator implements Module.Activator {

	public static Trie PKGNAME_CONFIG_OPTION = Trie.fromString("package/name");
	public static Trie SOURCE_CONFIG_OPTION = Trie.fromString("build/whiley/target");
	public static Trie TARGET_CONFIG_OPTION = Trie.fromString("build/boogie/target");
	public static Trie VERIFY_CONFIG_OPTION = Trie.fromString("build/boogie/verify");
	public static Trie VERBOSE_CONFIG_OPTION = Trie.fromString("build/boogie/verbose");
	public static Trie TIMEOUT_CONFIG_OPTION = Trie.fromString("build/boogie/timeout");
	private static Value.UTF8 TARGET_DEFAULT = new Value.UTF8("bin".getBytes());

	public static Command.Platform BOOGIE_PLATFORM = new Command.Platform() {
		//
		@Override
		public String getName() {
			return "boogie2";
		}

		@Override
		public Configuration.Schema getConfigurationSchema() {
			return Configuration.fromArray(
					Configuration.UNBOUND_STRING(TARGET_CONFIG_OPTION, "Specify location for generated Boogie .bpl files", TARGET_DEFAULT),
					Configuration.UNBOUND_BOOLEAN(VERIFY_CONFIG_OPTION, "Enable verification of Whiley files using Boogie", new Value.Bool(true)),
					Configuration.UNBOUND_BOOLEAN(VERBOSE_CONFIG_OPTION, "Enable verbose output", new Value.Bool(false)),
					Configuration.UNBOUND_INTEGER(TIMEOUT_CONFIG_OPTION, "Set timeout limit (ms)", new Value.Int(10000))
			);
		}

		@Override
		public void initialise(Configuration configuration, Command.Project project) throws IOException {
			Trie pkg = Trie.fromString(configuration.get(Value.UTF8.class, PKGNAME_CONFIG_OPTION).unwrap());
			// Specify directory where generated Boogie files are dumped.
			Trie source = Trie.fromString(configuration.get(Value.UTF8.class, SOURCE_CONFIG_OPTION).unwrap());
			// Construct the source root
			Path.Root sourceRoot = project.getRoot().createRelativeRoot(source);
			// Register build target for this package
			registerBuildTarget(configuration, project, sourceRoot, pkg);
		}

		private void registerBuildTarget(Configuration configuration, Build.Project project, Path.Root sourceRoot,
				Trie pkg) throws IOException {
			// Specify directory where generated JS files are dumped.
			Trie target= Trie.fromString(configuration.get(Value.UTF8.class, TARGET_CONFIG_OPTION).unwrap());
			// Determine whether verification enabled or not
			boolean verification = configuration.get(Value.Bool.class, VERIFY_CONFIG_OPTION).unwrap();
			// Determine whether verbose output enabled or not
			boolean verbose = configuration.get(Value.Bool.class, VERBOSE_CONFIG_OPTION).unwrap();
			// Determine timeout to use
			BigInteger timeout = configuration.get(Value.Int.class, TIMEOUT_CONFIG_OPTION).unwrap();
			// Construct the binary root
			Path.Root binaryRoot = project.getRoot().createRelativeRoot(target);
			// Initialise the target file being built
			Path.Entry<BoogieFile> binary = initialiseBinaryTarget(binaryRoot,pkg);
			// Specify set of files included
			Content.Filter<WyilFile> wyilIncludes = Content.filter("**", WyilFile.ContentType);
			//
			project.getRules().add(new AbstractBuildRule<WyilFile, BoogieFile>(sourceRoot, wyilIncludes, null) {
				@Override
				protected void apply(List<Path.Entry<WyilFile>> matches, Collection<Build.Task> tasks)
						throws IOException {
					// Construct a new build task
					BoogieCompileTask task = new BoogieCompileTask(project, binary, matches.get(0));
					// Configure task
					task.setVerbose(verbose);
					task.setVerification(verification);
					task.setTimeout(timeout.intValueExact());
					// Submit the task for execution
					tasks.add(task);
				}
			});
		}

		@Override
		public Content.Type<?> getSourceType() {
			return WyilFile.ContentType;
		}

		@Override
		public Content.Type<?> getTargetType() {
			return BoogieFile.ContentType;
		}

		@Override
		public void execute(Build.Project project, Path.ID id, String method, Value... args) throws IOException {
			throw new UnsupportedOperationException("Execute not supported");
		}

		private Path.Entry<BoogieFile> initialiseBinaryTarget(Path.Root binroot, Path.ID id) throws IOException {
			Path.Entry<BoogieFile> target;
			//
			if(binroot.exists(id, BoogieFile.ContentType)) {
				// Yes, it does so reuse it.
				target = binroot.get(id, BoogieFile.ContentType);
			} else {
				// No, it doesn't so create and initialise it
				target = binroot.create(id, BoogieFile.ContentType);
			}
			// Initialise with empty Boogie file
			BoogieFile jsf = new BoogieFile();
			// Write
			target.write(jsf);
			// Done
			return target;
		}
	};

	// =======================================================================
	// Start
	// =======================================================================

	@Override
	public Module start(Module.Context context) {
		// Register platform
		context.register(Command.Platform.class, BOOGIE_PLATFORM);
		// List of content types
		context.register(Content.Type.class, BoogieFile.ContentType);
		// Done
		return new Module() {
			// what goes here?
		};
	}

	// =======================================================================
	// Stop
	// =======================================================================

	@Override
	public void stop(Module module, Module.Context context) {
		// could do more here?
	}
}
