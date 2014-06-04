package de.ovgu.contracts.builder.compiler;

import java.util.LinkedList;
import java.util.List;

/**
 * Compiles runtime assertions.
 * @author Jens Meinicke
 *
 */
public class RACompiler extends AbstractCompiler {
    
    private static final String SEPARATOR = System.getProperty("path.separator");
    
    // java -jar openjml.jar -rac -noPurityCheck B.java 
    public final void compile(final String source, final String destiantion) {
        final List<String> options = new LinkedList<String>();
        options.add("java");
        options.add("-jar");
        options.add(LIB_PATH + "jml\\openjml.jar");
        options.add("-noInternalSpecs");
        options.add("-racCompileToJavaAssert"); // This works :)
        options.add("-rac");
        options.add("-noPurityCheck");
        
        options.add("-cp");
        options.add(LIB_PATH + "jpf.jar"
                + SEPARATOR + LIB_PATH + "jml\\jmlspecs.jar"
                + SEPARATOR + LIB_PATH + "jml\\openjml.jar"
                + SEPARATOR + LIB_PATH + "jml\\jmlruntime.jar"
                + SEPARATOR + LIB_PATH + "jpf-classes.jar"
                + SEPARATOR + LIB_PATH + "RunJPF.jar"
                + SEPARATOR + LIB_PATH + "RunTest.jar"
                + SEPARATOR + LIB_PATH + "jpf-annotations.jar"
                + SEPARATOR + LIB_PATH + "jpf-bdd-annotations.jar"
                + SEPARATOR + LIB_PATH + "jpf-bdd.jar"
                + SEPARATOR + LIB_PATH + "RunAnt.jar");
        
        options.add("-d");
        options.add(destiantion);
        
        options.add("-dir");
        options.add(source);
        process(options);
    }

}
