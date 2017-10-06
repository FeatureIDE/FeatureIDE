/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ahead.errorpropagation;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.Scanner;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.ahead.wrapper.AheadBuildErrorEvent;
import de.ovgu.featureide.core.CorePlugin;

/**
 * Tests the class {@link AheadBuildErrorEvent}<br><br>
 *
 * To generate test cases copy the files into "testcases.<code>projectname</code>"<br> java files need to be renamed into <code>filename</code>.javaX<br>
 * feature files need to be renamed into <code>feature</code>_filename.jak
 *
 * @author Jens Meinicke
 */
/*
 * A full test could be possible checking all lines of a generated file and compares the content of the lines (except for lines whose content needed to be
 * changed or is created at the composition process)
 */
public class TAheadErrorPropagation {

	AheadBuildErrorEvent event = new AheadBuildErrorEvent();

	private String project;

	private void setHelloWorld() {
		project = "HelloWorld";
	}

	private void setDesktopSearcher() {
		project = "DesktopSearcher";
	}

	public File getFile(String name) {
		final File folder = Commons.getTestCaseFolder().listFiles(getFileFilter(project))[0];
		return folder.listFiles(getFileFilter(name))[0];
	}

	private final static FileFilter getFileFilter(final String s) {
		return new FileFilter() {

			@Override
			public boolean accept(File pathname) {
				return pathname.getName().equals(s);
			}
		};
	}

	/**
	 * Main test function. Calls all necessary methods to generate the markers.
	 *
	 * @param className The name of the class.
	 * @param feature The feature containing the error
	 * @param javaLine The line at the generated java file
	 * @param composedLine The line at the composed jak file
	 * @param jakLine The line at the source file
	 */
	private void test(String className, String feature, int javaLine, int composedLine, int jakLine) {
		final int composedJakLine = calculateComposedJakLine(javaLine, className + ".javaX");
		if (composedLine != composedJakLine) {
			System.out.println("Wrong composed line @ " + className + ".java (expected: " + composedLine + " but was: " + composedJakLine + ")");
		}

		final String content = readFile(getFile(className + ".jak"));
		final int line = event.setSourceFile(content, composedJakLine);

		if (!event.fileName.equals("../features/" + feature + "/" + className + ".jak")) {
			System.out.println("Wrong source files @ " + className + ".java (expected: " + "../features/" + feature + "/" + className + ".jak" + " but was: "
				+ event.fileName + ")");
		}

		final int sourceLine = event.setSourceLine(composedJakLine, line, readFile(getFile(feature + "_" + className + ".jak")));
		if (jakLine != sourceLine) {
			System.out.println("Wrong source line @ " + className + ".java (expected: " + jakLine + " but was: " + sourceLine + ")");
		}
		// TODO #457 AHEAD error propagation add this test
		// assertEquals(jakLine, sourceLine);
	}

	private int calculateComposedJakLine(int javaLine, String fileName) {
		return event.calculateComposedJakLine(javaLine, readFile(getFile(fileName)));
	}

	private String readFile(File file) {
		Scanner scanner = null;
		final StringBuilder builder = new StringBuilder();
		try {
			scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				builder.append(scanner.nextLine());
				builder.append("\r\n");
			}
		} catch (final FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return builder.toString();
	}

	/*
	 * �********************************************************************** project : HelloWorld-AHEAD * class : Main * configuration : BeatifulWorld *
	 ************************************************************************/
	@Test
	public void testMain_1() {
		setHelloWorld();
		test("Main", "Hello", 6, 6, 4);
	}

	@Test
	public void testMain_2() {
		setHelloWorld();
		test("Main", "Beautiful", 18, 18, 4);
	}

	@Test
	public void testMain_3() {
		setHelloWorld();
		test("Main", "World", 27, 27, 4);
	}

	/*
	 * �********************************************************************** project : DesktopSearcher-AHEAD * class : MainFrame * configuration : config *
	 ************************************************************************/
	@Test
	public void testMainFrame_1() {
		setDesktopSearcher();
		test("MainFrame", "GUI", 48, 48, 37);
	}

	@Test
	public void testMainFrame_2() {
		setDesktopSearcher();
		test("MainFrame", "Single_Directory", 213, 213, 37);
	}

	@Test
	public void testMainFrame_3() {
		setDesktopSearcher();
		test("MainFrame", "Tree_View", 303, 291, 14);
	}
}
