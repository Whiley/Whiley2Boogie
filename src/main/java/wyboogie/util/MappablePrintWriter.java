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
package wyboogie.util;

import java.io.OutputStream;
import java.io.PrintWriter;

public class MappablePrintWriter<T> {
	private final PrintWriter out;
	
	public MappablePrintWriter(PrintWriter writer) {
		this.out = writer;
	}
	
	public MappablePrintWriter(OutputStream os) {
		this.out = new PrintWriter(os);
	}
	
	/**
	 * Print a string associated with a given tag.
	 * 
	 * @param text
	 * @param tag
	 */
	public void print(String text, T tag) {
		out.print(text);
	}
	
	/**
	 * Print a string associated with a given tag, followed by a newline.
	 * 
	 * @param text
	 * @param tag
	 */
	public void println(String text, T tag) {
		out.println(text);
	}
	
	/**
	 * Print a newline.
	 */
	public void println() {
		out.println();
	}
	
	/**
	 * Print a given level of indentation.
	 * 
	 * @param n
	 */
	public void tab(int n) {
		for(int i=0;i!=n;++i) {
			out.print("   ");
		}
	}
	
	/**
	 * Flushes the stream
	 */
	public void flush() {
		out.flush();
	}
	
	public void close() {
		out.close();
	}
}
