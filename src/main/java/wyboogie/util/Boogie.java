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

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;

import wyboogie.core.BoogieFile;
import wyboogie.io.BoogieFilePrinter;
import wybs.lang.SyntacticException;
import wyfs.util.ArrayUtils;

/**
 * A wrapper for the "boogie" verifier.
 *
 * @author David J. Pearce
 */
public class Boogie {
    private static final String BOOGIE_COMMAND = "boogie";

    public static final int ERROR_UNKNOWN_FAILURE = 5000;
    public static final int ERROR_ASSERTION_FAILURE = 5001;
    public static final int ERROR_PRECONDITION_FAILURE = 5002;
    public static final int ERROR_POSTCONDITION_FAILURE = 5003;
    public static final int ERROR_ESTABLISH_LOOP_INVARIANT_FAILURE = 5004;
    public static final int ERROR_RESTORE_LOOP_INVARIANT_FAILURE = 5005;

    private final String boogieCmd;

    /**
     * Record command-line options.
     */
    public final Map<String, String> options;

    public Boogie() {
        this(BOOGIE_COMMAND);
    }

    public Boogie(String command) {
        this.boogieCmd = command;
        this.options = new HashMap<>();
    }

    /**
     * Control printing of enhanced error messages. If enabled then print Z3 error model enhanced error messages.
     *
     * @param flag
     */
    public void setEnchancedErrorMessages(boolean flag) {
        options.put("enhancedErrorMessages", flag ? "1" : "0");
    }

    /**
     * Limit the number of seconds spent trying to verify each procedure
     *
     * @param seconds
     */
    public void setTimeLimit(int seconds) {
        options.put("timeLimit", Integer.toString(seconds));
    }

    /**
     * Enable the built-in array theory.
     */
    public Boogie setArrayTheory() {
        options.put("useArrayTheory", null);
        return this;
    }

    /**
     * Check a given filename
     *
     * @param timeout (in milli seconds)
     * @param boogie  Boogie contents (as a string)
     * @return
     */
    public Message[] check(int timeout, String id, BoogieFile boogie) {
        String filename = null;
        try {
            // Convert the boogie file into a byte sequence
            ByteArrayOutputStream output = new ByteArrayOutputStream();
            BoogieFilePrinter bfp = new BoogieFilePrinter(output);
            bfp.write(boogie);
            bfp.flush();
            byte[] bytes = output.toByteArray();
            // Create the temporary file.
            filename = createTemporaryFile(id, ".bpl", bytes);
            // ===================================================
            // Construct command
            // ===================================================
            ArrayList<String> command = new ArrayList<>();
            command.add(boogieCmd);
            // Add any registered command-line options
            for (Map.Entry<String, String> e : options.entrySet()) {
                String opt = e.getKey();
                String val = e.getValue();
                if (val == null) {
                    command.add("/" + opt);
                } else {
                    command.add("/" + opt + ":" + val);
                }
            }
            command.add(filename);
            // ===================================================
            // Construct the process
            // ===================================================
            ProcessBuilder builder = new ProcessBuilder(command);
            Process child = builder.start();
            try {
                // second, read the result whilst checking for a timeout
                InputStream input = child.getInputStream();
                InputStream error = child.getErrorStream();
                boolean success = child.waitFor(timeout, TimeUnit.MILLISECONDS);
                byte[] stdout = readInputStream(input);
                byte[] stderr = readInputStream(error);
                if (success && child.exitValue() == 0) {
                    return parseErrors(new String(stdout), bfp.getMapping());
                }
            } finally {
                // make sure child process is destroyed.
                child.destroy();
            }
        } catch (IOException e) {
            throw new RuntimeException(e.getMessage(), e);
        } catch (InterruptedException e) {
            throw new RuntimeException(e.getMessage(), e);
        } finally {
            if (filename != null) {
                // delete the temporary file
                new File(filename).delete();
            }
        }
        return null;
    }

    public static interface Message {
    }

    public static class FatalError implements Message {

    }

    public static class Error implements Message {
        private final int line;
        private final int column;
        private final String message;
        private final BoogieFile.Item item;

        public Error(int line, int col, String message, BoogieFile.Item item) {
            this.line = line;
            this.column = col;
            this.message = message;
            this.item = item;
        }

        /**
         * Get the line number of this error.
         *
         * @return
         */
        public int getLine() {
            return line;
        }

        /**
         * Get the column number within the given line where this error occurs.
         *
         * @return
         */
        public int getColumn() {
            return column;
        }

        /**
         * Get the error code associated with this message.
         *
         * @return
         */
        public int getCode() {
            // Attempt to convert back into error codes based on the error message reported.  This is a little hackery,
            // and its annoying that Boogie dropped error codes from messages.
            if (message.contains("assertion")) {
                return ERROR_ASSERTION_FAILURE;
            } else if (message.contains("postcondition")) {
                return ERROR_POSTCONDITION_FAILURE;
            } else if (message.contains("precondition")) {
                return ERROR_PRECONDITION_FAILURE;
            } else if (message.contains("loop invariant")) {
                if (message.contains("maintained")) {
                    return ERROR_RESTORE_LOOP_INVARIANT_FAILURE;
                } else {
                    return ERROR_ESTABLISH_LOOP_INVARIANT_FAILURE;
                }
            }
            //
            return ERROR_UNKNOWN_FAILURE;
        }

        /**
         * Get the error message.
         *
         * @return
         */
        public String getMessage() {
            return message;
        }

        /**
         * Get the item associated with this error message.
         *
         * @return
         */
        public BoogieFile.Item getEnclosingItem() {
            return item;
        }

        @Override
        public String toString() {
            return Integer.toString(line) + ":" + column + ":" + message;
        }
    }

    /**
     * Parse Standard Output from Boogie into a useful form.
     *
     * @param output
     * @return
     */
    private static Message[] parseErrors(String output, MappablePrintWriter.Mapping<BoogieFile.Item> m) {
        String[] lines = output.split("\n");
        Message[] errors = new Message[lines.length];
        for (int i = 0; i != lines.length; ++i) {
            // Decode boogie error line
            String ith = lines[i];
            if (ith.startsWith("Fatal Error:")) {
                errors[i] = new FatalError();
                break;
            } else {
                int a = ith.indexOf('(');
                int b = ith.indexOf(',');
                int c = ith.indexOf(')');
                int d = ith.indexOf(':');
                int e = ith.indexOf("Error:");
                if (a >= 0 && b >= 0 && c >= 0 && d >= 0 && e >= 0) {
                    int line = Integer.parseInt(ith.substring(a + 1, b));
                    int col = Integer.parseInt(ith.substring(b + 1, c));
                    String message = ith.substring(e + 6);
                    BoogieFile.Item item = m.get(line, col);
                    errors[i] = new Error(line, col, message, item);
                }
            }
        }

        return ArrayUtils.removeAll(errors, null);
    }

    /**
     * Write a given string into a temporary file which can then be checked by boogie.
     *
     * @param contents
     * @return
     */
    private static String createTemporaryFile(String prefix, String suffix, byte[] contents)
            throws IOException, InterruptedException {
        // Create new file
        File f = File.createTempFile(prefix, suffix);
        // Open for writing
        FileOutputStream fout = new FileOutputStream(f);
        // Write contents to file
        fout.write(contents);
        // Done creating file
        fout.close();
        //
        return f.getAbsolutePath();
    }


    /**
     * Read an input stream entirely into a byte array.
     *
     * @param input
     * @return
     * @throws IOException
     */
    private static byte[] readInputStream(InputStream input) throws IOException {
        byte[] buffer = new byte[1024];
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        while (input.available() > 0) {
            int count = input.read(buffer);
            output.write(buffer, 0, count);
        }
        return output.toByteArray();
    }
}
