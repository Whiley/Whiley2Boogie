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

import wyboogie.core.BoogieFile;

import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.*;

public class MappablePrintWriter<T> {
	private final PrintWriter out;
	private final Mapping<T> mapping;
	private int index;

	public MappablePrintWriter(OutputStream os) {
		this(new PrintWriter(os));
	}

	public MappablePrintWriter(PrintWriter writer) {
		this.out = writer;
		this.mapping = new Mapping<T>();
	}

	public Mapping getMapping() {
		return mapping;
	}

	/**
	 * Print a string associated with a given tag.
	 * 
	 * @param text
	 * @param tag
	 */
	public void print(String text, T tag) {
		out.print(text);
		mapping.put(tag,index,text.length());
		index += text.length();
	}

	/**
	 * Print a newline.
	 */
	public void println() {
		out.println();
		mapping.newLine();
		index = 0;
	}

	/**
	 * Print a string associated with a given tag, followed by a newline.
	 * 
	 * @param text
	 * @param tag
	 */
	public void println(String text, T tag) {
		print(text,tag);
		println();
	}

	/**
	 * Print a given level of indentation.
	 * 
	 * @param n
	 */
	public void tab(int n) {
		for(int i=0;i!=n;++i) {
			out.print("   ");
			index += 3;
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

	public static class Mapping<T> {
		private ArrayList<ArrayList<Span>> lines = new ArrayList<>();

		public Mapping() {
			newLine();
		}

		public void put(T tag, int start, int length) {
			int end = (start + length) - 1;
			ArrayList<Span> line = lines.get(lines.size()-1);
			line.add(new Span(tag,start,end));
		}

		public void newLine() {
			lines.add(new ArrayList<>());
		}

		public T get(int line, int col) {
			// Account for line numbers which start from 1
			line = line - 1;
			//
			if(line >= lines.size()) {
				return null;
			} else {
				List<Span> l = lines.get(line);
				for(int i=0;i!=l.size();++i) {
					Span<T> s = l.get(i);
					if(s.contains(col)) {
						return s.tag;
					}
				}
				return null;
			}
		}
	}


	/**
	 * Represents a given region of text.
	 */
	public static class Span<T> {
		private final T tag;
		private final int start;
		private final int end;

		public Span(T tag, int start, int end) {
			this.tag = tag;
			this.start = start;
			this.end = end;
		}

		public boolean contains(int col) {
			return start <= col && col <= end;
		}
	}
}
