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
import wyil.lang.WyilFile;

public class BoogieBuildTask implements Build.Task {
	private final Build.Meter meter = Build.NULL_METER;
	/**
	 * The source file that this task will compiler from.
	 */
	private final Trie source;
	/**
	 * Identifier for target of this build task.
	 */
	private final Trie target;
	/**
	 * Specify debugging mode (this disables mangling, etc)
	 */
	private boolean debug = false;

	public BoogieBuildTask(Trie target, Trie source) {
		if(target == null) {
			throw new IllegalArgumentException("invalid target");
		} else if(source == null) {
			throw new IllegalArgumentException("invalid source");
		}
		this.target = target;
		this.source = source;
	}

	public BoogieBuildTask setDebug(boolean flag) {
		this.debug = flag;
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
		BoogieFile target = new BoogieFile(this.target);
		BoogieCompiler bc = new BoogieCompiler(meter,target);
		// Configure debug mode (if applicable)
		bc.setMangling(!debug);
		// Run the translation!
		bc.visitModule(binary);
		// Write target into snapshot
		snapshot = snapshot.put(target);
		//
		return new Pair<>(snapshot,true);
	}
}
