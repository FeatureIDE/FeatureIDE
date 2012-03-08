package org.sonatype.plugins.munge;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.StreamTokenizer;
import java.io.StringWriter;
import java.util.EmptyStackException;
import java.util.Hashtable;
import java.util.NoSuchElementException;
import java.util.Stack;
import java.util.StringTokenizer;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.munge.MungeCorePlugin;

/*
 * The contents of this file are subject to the terms of the Common Development
 * and Distribution License (the License). You may not use this file except in
 * compliance with the License.
 *
 * You can obtain a copy of the License at http://www.netbeans.org/cddl.html
 * or http://www.netbeans.org/cddl.txt.
 *
 * When distributing Covered Code, include this CDDL Header Notice in each file
 * and include the License file at http://www.netbeans.org/cddl.txt.
 * If applicable, add the following below the CDDL Header, with the fields
 * enclosed by brackets [] replaced by your own identifying information:
 * "Portions Copyrighted [year] [name of copyright owner]"
 *
 * The Original Software is NetBeans. The Initial Developer of the Original
 * Software is Sun Microsystems, Inc. Portions Copyright 1997-2006 Sun
 * Microsystems, Inc. All Rights Reserved.
 */



/**
 * Munge: a purposely-simple Java preprocessor.  It only 
 * supports conditional inclusion of source based on defined strings of 
 * the form "if[tag]",
 * "if_not[tag]", "else[tag], and "end[tag]".  Unlike traditional 
 * preprocessors, comments and formatting are all preserved for the 
 * included lines.  This is on purpose, as the output of Munge
 * will be distributed as human-readable source code.
 * <p>
 * To avoid creating a separate Java dialect, the conditional tags are
 * contained in Java comments.  This allows one build to compile the
 * source files without pre-processing, to facilitate faster incremental
 * development.  Other builds from the same source have their code contained 
 * within that comment.  The format of the tags is a little verbose, so 
 * that the tags won't accidentally be used by other comment readers
 * such as javadoc.  Munge tags <b>must</b> be in C-style comments; 
 * C++-style comments may be used to comment code within a comment.
 *
 * <p>
 * To demonstrate this, our sample source has 1.1 and 1.2-specific code,
 * with 1.1 as the default build:
 * <pre><code>
 *     public void setSystemProperty(String key, String value) {
 *         &#47;*if[JDK1.1]*&#47;
 *         Properties props = System.getProperties();
 *         props.setProperty(key, value);
 *         System.setProperties(props);
 *         &#47;*end[JDK1.1]*&#47;
 * <p>
 *         &#47;*if[JDK1.2]
 *         // Use the new System method.
 *         System.setProperty(key, value);
 *           end[JDK1.2]*&#47;
 *     }
 * </code></pre>
 * <p>
 * When the above code is directly compiled, the code bracketed by
 * the JDK1.1 tags will be used.  If the file is run through 
 * Munge with the JDK1.2 tag defined, the second code block 
 * will used instead. This code can also be written as:
 * <pre><code>
 *     public void setSystemProperty(String key, String value) {
 *         &#47;*if[JDK1.2]
 *         // Use the new System method.
 *         System.setProperty(key, value);
 *           else[JDK1.2]*&#47;
 * <p>
 *         Properties props = System.getProperties();
 *         props.setProperty(key, value);
 *         System.setProperties(props);
 *         &#47;*end[JDK1.2]*&#47;
 *     }
 * </code></pre>
 *
 * Munge also performs text substitution; the Swing build uses this to
 * convert its package references from <code>javax.swing</code>
 * to <code>java.awt.swing</code>, for example.  This substitution is
 * has no knowledge of Java syntax, so only use it to convert strings
 * which are unambiguous.  Substitutions are made in the same order as
 * the arguments are specified, so the first substitution is made over
 * the whole file before the second one, and so on.
 * <p>
 * Munge's command line takes one of the following forms:
 * <pre><code>
 *    java Munge [-D&lt;symbol&gt; ...] [-s &lt;old&gt;=&lt;new&gt; ...] [&lt;in file&gt;] [&lt;out file&gt;]
 *    java Munge [-D&lt;symbol&gt; ...] [-s &lt;old&gt;=&lt;new&gt; ...] &lt;file&gt; ... &lt;directory&gt;
 * </code></pre>
 * <p>
 * In the first form, if no output file is given, System.out is used.  If
 * neither input nor output file are given, System.in and System.out are used.
 * Munge can also take an <code>@&lt;cmdfile&gt;</code> argument.  If one is
* specified then the given file is read for additional command line arguments.
* <p>
* Like any preprocessor, developers must be careful not to abuse its
* capabilities so that their code becomes unreadable.  Please use it
* as little as possible.
*
* @author: Thomas Ball
* @author: Joerg Liebig (Nesting)
* @version: 1.7 98/10/13
*/
public class Munge {

    static Hashtable<String, Object> symbols = new Hashtable<String, Object>(2);

    static Vector<String> oldTextStrings = new Vector<String>();
    static Vector<String> newTextStrings = new Vector<String>();

    int errors = 0;
    int line = 1;
    String inName;
    BufferedReader in;
    PrintWriter out;
    Stack<Boolean> stack = new Stack<Boolean>();
    boolean printing = true;
    String source = null;
    String block = null;

    final String[] commands = { "if", "if_not", "else", "end" };
    final int IF = 0;
    final int IF_NOT = 1;
    final int ELSE = 2;
    final int END = 3;
    final int numCommands = 4;

    final int EOF = 0;
    final int COMMENT = 1;     // text surrounded by /* */ delimiters
    final int CODE = 2;        // can just be whitespace

    private IFeatureProject featureProject;

    int getCommand(String s) {
        for (int i = 0; i < numCommands; i++) {
            if (s.equals(commands[i])) {
                return i;
            }
        }
        return -1;
    }

    public void error(String text) {
        addMarker(text, getFile(inName), line);
        errors++;
    }

    /**
     * @param inName2
     * @return
     */
    private IFile getFile(String inName) {
        inName = inName.substring(inName.indexOf(featureProject.getProjectName() + "\\")
                + featureProject.getProjectName().length() + 1);
        inName = inName.substring(inName.indexOf(featureProject.getSourceFolder().getName() + "\\")
                + featureProject.getSourceFolder().getName().length() + 1);

        IFolder folder = featureProject.getSourceFolder();
        while (inName.contains("\\")) {
            folder = folder.getFolder(inName.substring(0, inName.indexOf('\\')));
        }

        return folder.getFile(inName);
    }

    public void addMarker(final String text, final IFile file, final int line) {
        Job job = new Job("Propagate syntax markers") {
            @Override
                public IStatus run(IProgressMonitor monitor) {
                    try {

                        if (!hasMarker()) {
                            IMarker newMarker = file.createMarker(CorePlugin.PLUGIN_ID + ".builderProblemMarker");
                            newMarker.setAttribute(IMarker.LINE_NUMBER, line);
                            newMarker.setAttribute(IMarker.MESSAGE, text);
                            newMarker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
                        }
                    } catch (CoreException e) {
                        MungeCorePlugin.getDefault().logError(e);
                    }
                    return Status.OK_STATUS;
                }

            private boolean hasMarker() {
                try {
                    IMarker[] marker = file.findMarkers(CorePlugin.PLUGIN_ID + ".builderProblemMarker"
                            , false, IResource.DEPTH_ZERO);
                    if (marker.length > 0) {
                        for (IMarker m : marker) {
                            if (line == m.getAttribute(IMarker.LINE_NUMBER, -1)) {
                                if (text.equals(m.getAttribute(IMarker.MESSAGE, null))) {
                                    return true;
                                }
                            }
                        }
                    }
                } catch (CoreException e) {
                    MungeCorePlugin.getDefault().logError(e);
                }
                return false;
            }
        };
        job.setPriority(Job.DECORATE);
        job.schedule();
    }

    public void printErrorCount() {
    }

    public boolean hasErrors() {
        return (errors > 0);
    }

    public Munge(String inName, String outName, IFeatureProject featureProject) {
        this.featureProject = featureProject;
        this.inName = inName;
        if( inName == null ) {
            in = new BufferedReader( new InputStreamReader(System.in) );
        } else {
            try {
                in = new BufferedReader( new FileReader(inName) );
            } catch (FileNotFoundException fnf) {
                MungeCorePlugin.getDefault().logWarning("Cannot find input file " + inName);
                errors++;
                return;
            }
        }

        if( outName == null ) {
            out = new PrintWriter(System.out);
        } else {
            try {
                out = new PrintWriter( new FileWriter(outName) );
            } catch (IOException ioe) {
                MungeCorePlugin.getDefault().logError("Cannot write to file " + outName, ioe);
                errors++;
            }
        }
    }

    public Munge() {

    }

    private void checkNesting() {
        if (stack.size() > 1) {
            printing = (Boolean) stack.peek() && printing;
        }
    }

    public void close() throws IOException {
        in.close();
        out.flush();
        out.close();
    }

    void cmd_if(String version) {
        Boolean b = new Boolean(printing);
        stack.push(b);
        printing = (symbols.get(version) != null);
        checkNesting();
    }

    void cmd_if_not(String version) {
        Boolean b = new Boolean(printing);
        stack.push(b);
        printing = (symbols.get(version) == null);
        checkNesting();
    }

    void cmd_else() {
        printing = !printing;
        checkNesting();
    }

    void cmd_end() throws EmptyStackException {
        Boolean b = (Boolean)stack.pop();
        printing = b.booleanValue();
    }

    void print(String s) throws IOException {
        if (printing) {
            out.write(s);
        } else {
            // Output empty lines to preserve line numbering.
            int n = countLines(s);
            for (int i = 0; i < n; i++) {
                out.write('\n');
            }
        }
    }

    // Return the number of line endings in a string.
    int countLines(String s) {
        int i = 0;
        int n = 0;
        while ((i = block.indexOf('\n', i) + 1) > 0) {
            n++;
        }
        return n;
    }

    /*
     * If there's a preprocessor tag in this comment, act on it and return
     * any text within it.  If not, just return the whole comment unchanged.
     */
    void processComment(String comment) throws IOException {
        String commentText = comment.substring(2, comment.length() - 2);
        StringTokenizer st = new StringTokenizer(
                commentText, "[] \t\r\n", true);
        boolean foundTag = false;
        StringBuilder buffer = new StringBuilder();

        try {
            while (st.hasMoreTokens()) {
                String token = st.nextToken();
                int cmd = getCommand(token);
                if (cmd == -1) {
                    buffer.append(token);
                    if (token.equals("\n")) {
                        line++;
                    }
                } else {
                    token = st.nextToken();
                    if (!token.equals("[")) {
                        // Not a real tag: save it and continue...
                        buffer.append(commands[cmd]);
                        buffer.append(token);
                    } else {
                        String symbol = st.nextToken();
                        if (!st.nextToken().equals("]")) {
                            error("invalid preprocessor statement");
                        }
                        foundTag = true;

                        // flush text, as command may change printing state
                        print(buffer.toString());
                        buffer.setLength(0);  // reset buffer

                        switch (cmd) {
                            case IF:
                                cmd_if(symbol);
                                break;
                            case IF_NOT:
                                cmd_if_not(symbol);
                                break;
                            case ELSE:
                                cmd_else();
                                break;
                            case END:
                                cmd_end();
                                break;
                            default:
                                throw new InternalError("bad command");
                        }
                    }
                }
            }
        } catch (NoSuchElementException nse) {
            error("invalid preprocessor statement");
        } catch (EmptyStackException ese) {
            error("unmatched end or else statement");
        }

        if (foundTag) {
            print(buffer.toString());
        } else {
            print(comment);
        }
    }

    // Munge views a Java source file as consisting of 
    // blocks, alternating between comments and the text between them.
    int nextBlock() throws IOException {
        if (source == null || source.length() == 0) {
            block = null;
            return EOF;
        }
        if (source.startsWith("/*")) {
            // Return comment as next block.
            int i = source.indexOf("*/");
            if (i == -1) {
                // malformed comment, skip
                block = source;
                return CODE;
            }
            i += 2;  // include comment close
            block = source.substring(0, i);
            source = source.substring(i);
            return COMMENT;
        }

        // Return text up to next comment, or rest of file if no more comments.
        int i = source.indexOf("/*");
        if (i != -1) {
            block = source.substring(0, i);
            source = source.substring(i);
        } else {
            block = source;
            source = null;
        }

        // Update line count -- this isn't done for comments because
        // line counting has to be done during parsing.
        line += countLines(block);

        return CODE;
    }

    void substitute() {
        for (int i = 0; i < oldTextStrings.size(); i++) {
            String oldText = (String)oldTextStrings.elementAt(i);
            String newText = (String)newTextStrings.elementAt(i);
            int n;
            while ((n = source.indexOf(oldText)) >= 0) {
                source = source.substring(0, n) + newText + 
                    source.substring(n + oldText.length());
            }
        }
    }

    public void process() throws IOException {
        // Read all of file into a single stream for easier scanning.
        StringWriter sw = new StringWriter();
        char[] buffer = new char[8192];
        int n;
        while ((n = in.read(buffer, 0, 8192)) > 0) {
            sw.write(buffer, 0, n);
        }
        source = sw.toString();

        // Perform any text substitutions.
        substitute();

        // Do preprocessing.
        int blockType;
        do {
            blockType = nextBlock();
            if (blockType == COMMENT) {
                processComment(block);
            } else if (blockType == CODE) {
                print(block);
            }
        } while (blockType != EOF);

        // Make sure any conditional statements were closed.
        if (!stack.empty()) {
            error("missing end statement(s)");
        }
    }

    /**
     * Report how this utility is used and exit.
     */
    public static void usage() {
        MungeCorePlugin.getDefault().logWarning("usage:" +
                "\n    java Munge [-D<symbol> ...] " +
                "[-s <old>=<new> ...] " + 
                "[<in file>] [<out file>]" +
                "\n    java Munge [-D<symbol> ...] " +
                "[-s <old>=<new> ...] " + 
                "<file> ... <directory>"
                );
        //	System.exit(1);
    }
    public static void usage(String msg) {
        MungeCorePlugin.getDefault().logWarning(msg);
        usage();
    }

    /**
     * Munge's main entry point.
     */
    public void main(String[] args, IFeatureProject featureProject) {
        this.featureProject = featureProject;
        // Use a dummy object as the hash entry value.
        Object obj = new Object();

        // Replace and @file arguments with the contents of the specified file.
        try {
            args = CommandLine.parse( args );
        } catch( IOException e ) {
            MungeCorePlugin.getDefault().logError("Unable to read @file argument.", e);
        }

        // Load symbol definitions
        int iArg = 0;
        symbols.clear();
        while (iArg < args.length && args[iArg].startsWith("-")) {
            if (args[iArg].startsWith("-D")) {
                String symbol = args[iArg].substring(2);
                symbols.put(symbol, obj);
            }

            else if (args[iArg].equals("-s")) {
                if (iArg == args.length) {
                    usage("no substitution string specified for -s parameter");
                }

                // Parse and store <old_text>=<new_text> parameter.
                String subst = args[++iArg];
                int equals = subst.indexOf('=');
                if (equals < 1 || equals >= subst.length()) {
                    usage("invalid substitution string \"" + subst + "\"");
                }
                String oldText = subst.substring(0, equals);
                oldTextStrings.addElement(oldText);
                String newText = subst.substring(equals + 1);
                newTextStrings.addElement(newText);
            }

            else {
                usage("invalid flag \"" + args[iArg] + "\"");
            }

            iArg++;
        }

        // Parse file name arguments into an array of input file names and
        // output file names.
        String[] inFiles = new String[Math.max(args.length-iArg-1, 1)];
        String[] outFiles = new String[inFiles.length];

        if( iArg < args.length ) {
            File targetDir = new File( args[args.length-1] );
            if( targetDir.isDirectory() ) {
                int i = 0;
                for( ; iArg<args.length-1; i++, iArg++ ) {
                    inFiles[i] = args[iArg];
                    File inFile = new File( args[iArg] );
                    File outFile = new File( targetDir, inFile.getName() );
                    outFiles[i] = outFile.getAbsolutePath();
                }
                if( i == 0 ) {
                    usage("No source files specified.");
                }
            } else {            
                inFiles[0] = args[iArg++];
                if( iArg < args.length ) {
                    outFiles[0] = args[iArg++];
                } 
                if( iArg < args.length ) {
                    usage(args[args.length-1] + " is not a directory.");
                }                
            }
        }

        // Now do the munging.
        for( int i=0; i<inFiles.length; i++ ) {

            Munge munge = new Munge(inFiles[i], outFiles[i], featureProject);
            if (munge.hasErrors()) {
                munge.printErrorCount();

                //                System.exit(munge.errors);
            }

            try {
                munge.process();
                munge.close();
            } catch (IOException e) {
                MungeCorePlugin.getDefault().logError(e);
            }

            if (munge.hasErrors()) {
                munge.printErrorCount();
                //                System.exit(munge.errors);
            }
        }

        //	System.exit(0);
    }


    /**
     * This class was cut and pasted from the JDK1.2 sun.tools.util package.
     * Since Munge needs to be used when only a JRE is present, we could not
     * use it from that place. Likewise, Munge needs to be able to run under 1.1
     * so the 1.2 collections classes had to be replaced in this version.
     */
    static class CommandLine {
        /**
         * Process Win32-style command files for the specified command line
         * arguments and return the resulting arguments. A command file argument
         * is of the form '@file' where 'file' is the name of the file whose
         * contents are to be parsed for additional arguments. The contents of
         * the command file are parsed using StreamTokenizer and the original
         * '@file' argument replaced with the resulting tokens. Recursive command
         * files are not supported. The '@' character itself can be quoted with
         * the sequence '@@'.
         */
        static String[] parse(String[] args)
            throws IOException
            {
                Vector<String> newArgs = new Vector<String>(args.length);
                for (int i = 0; i < args.length; i++) {
                    String arg = args[i];
                    if (arg.length() > 1 && arg.charAt(0) == '@') {
                        arg = arg.substring(1);
                        if (arg.charAt(0) == '@') {
                            newArgs.addElement(arg);
                        } else {
                            loadCmdFile(arg, newArgs);
                        }
                    } else {
                        newArgs.addElement(arg);
                    }
                }
                String[] newArgsArray = new String[newArgs.size()];
                newArgs.copyInto(newArgsArray);
                return newArgsArray;
            }

        private static void loadCmdFile(String name, Vector<String> args)
            throws IOException
            {
                Reader r = new BufferedReader(new FileReader(name));
                StreamTokenizer st = new StreamTokenizer(r);
                st.resetSyntax();
                st.wordChars(' ', 255);
                st.whitespaceChars(0, ' ');
                st.commentChar('#');
                st.quoteChar('"');
                st.quoteChar('\'');
                while (st.nextToken() != StreamTokenizer.TT_EOF) {
                    args.addElement(st.sval);
                }
                r.close();
            }
    }
}
