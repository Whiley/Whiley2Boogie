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
package wy2boogie.tasks;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.function.Function;

import wy2boogie.core.BoogieFile;
import wybs.lang.Build;
import wybs.lang.Build.Meter;
import wybs.util.AbstractBuildTask;
import wyfs.lang.Path;
import wyil.lang.WyilFile;

public class BoogieCompileTask extends AbstractBuildTask<WyilFile, BoogieFile> {

	public BoogieCompileTask(Build.Project project, Path.Entry<BoogieFile> target, Path.Entry<WyilFile> source) {
		super(project, target, Arrays.asList(source));
	}

	public void setVerification(boolean flag) {
		throw new UnsupportedOperationException("implement BoogieCompileTask.setVerification()");
	}

	public void setCounterExamples(boolean flag) {
		throw new UnsupportedOperationException("implement BoogieCompileTask.setCounterExamples()");
	}

	@Override
	public Function<Meter,Boolean> initialise() throws IOException {
		// Extract target and source files for compilation. This is the component which
		// requires I/O.
		BoogieFile bf = target.read();
		WyilFile wyf = sources.get(0).read();
		// Construct the lambda for subsequent execution. This will eventually make its
		// way into some kind of execution pool, possibly for concurrent execution with
		// other tasks.
		return (Meter meter) -> execute(meter, bf, wyf);
	}

	/**
	 * The business end of a compilation task. The intention is that this
	 * computation can proceed without performing any blocking I/O. This means it
	 * can be used in e.g. a forkjoin task safely.
	 *
	 * @param target  --- The Boogie being written.
	 * @param sources --- The WyilFile(s) being translated.
	 * @return
	 */
	public boolean execute(Build.Meter meter, BoogieFile target, WyilFile... sources) {
		meter = meter.fork("BoogieCompiler");
		// Parse source files into target
		WyilFile source = sources[0];
		//
		new BoogieCompiler(meter,target).visitModule(source);
		//
		meter.done();
		//
		return true;
	}

}
