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
package wy2boogie.core;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.List;

import wyfs.lang.Content;
import wyfs.lang.Path;

public class BoogieFile {
	// =========================================================================
	// Content Type
	// =========================================================================

	/**
	 * Responsible for identifying and reading/writing WyilFiles. The normal
	 * extension is ".wyil" for WyilFiles.
	 */
	public static final Content.Type<BoogieFile> ContentType = new Content.Type<BoogieFile>() {
		public Path.Entry<BoogieFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<BoogieFile>) e;
			}
			return null;
		}

		@Override
		public BoogieFile read(Path.Entry<BoogieFile> e, InputStream input) throws IOException {
			throw new IllegalArgumentException("Implement BoogieFile.ContentType.read()");
		}

		@Override
		public void write(OutputStream output, BoogieFile bf) throws IOException {
			throw new IllegalArgumentException("Implement BoogieFile.ContentType.write()");
		}

		@Override
		public String toString() {
			return "Content-Type: boogie";
		}

		@Override
		public String getSuffix() {
			return "bpl";
		}
	};

	/**
	 * The list of top-level declarations within this file.
	 */
	private List<Declaration> declarations;

	public List<Declaration> getDeclarations() {
		return declarations;
	}

	// =========================================================================
	// Abstract Syntax Tree
	// =========================================================================

	public interface Term {

	}

	public interface Declaration {

	};
}
