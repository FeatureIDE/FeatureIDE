/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.contracts.builder.compiler;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

/**
 * Compiles with javac. 
 * @author Jens Meinicke
 *
 */
public class JavaCompiler extends AbstractCompiler {

	private static final String SEPARATOR = System.getProperty("path.separator");
	
	public final void compile(final String source, final String destiantion) {
		final List<File> files = getJavaFiles(new File(source));
		final List<String> options = new LinkedList<String>();
//		options.add("C:\\\"Program Files (x86)\"\\Java\\jre7_32\\bin\\javac.exe");
		options.add("C:\\Programme\\Java\\jdk1.7.0_21\\bin\\javac.exe");
		options.add("-g");
		options.add("-Xlint");
		options.add("-d");
		options.add(destiantion);
		options.add("-classpath");

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
				
		for (final File file : files) {
			options.add(file.getAbsolutePath());
		}
		process(options);
		
	}
	
	private List<File> getJavaFiles(final File source) {
		final List<File> files = new LinkedList<File>();
		for (final File file : source.listFiles()) {
			if (file.isDirectory()) {
				files.addAll(getJavaFiles(file));
			} else {
				if (file.getName().endsWith(".java")) {
					files.add(file);
				}
			}
		}
		return files;
	}

}
