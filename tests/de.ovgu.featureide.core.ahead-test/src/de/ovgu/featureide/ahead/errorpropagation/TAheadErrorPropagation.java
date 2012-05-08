package de.ovgu.featureide.ahead.errorpropagation;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.Scanner;

import org.junit.Test;

import de.ovgu.featureide.ahead.wrapper.AheadBuildErrorEvent;
import de.ovgu.featureide.core.CorePlugin;

import static org.junit.Assert.assertEquals;

/**
 * Tests the class {@link AheadBuildErrorEvent}<br><br>
 * 
 * To generate test cases copy the files into "testcases.<code>projectname</code>"<br>
 * java files need to be renamed into <code>filename</code>.javaX<br>
 * feature files need to be renamed into <code>feature</code>_filename.jak
 *  
 * @author Jens Meinicke
 * 
 */
/*
 * A full test could be possible checking all lines of a generated file and compares the content
 * of the lines (except for lines whose content needed to be changed or is created at the composition process)  
 */
public class TAheadErrorPropagation {

	protected static File FILE_FOLDER = new File(
			"/vol1/teamcity_itidb/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.core.ahead-test/src/testcases/");

	AheadBuildErrorEvent event = new AheadBuildErrorEvent();

	private String project;
	
	private void setHelloWorld() {
		project = "HelloWorld";
	}
	
	private void setDesktopSearcher() {
		project = "DesktopSearcher";
	}
	
	public File getFile(String name) {
		// first tries the location on build server, if this fails tries to use
		// local location
		if (!FILE_FOLDER.canRead()) {
			FILE_FOLDER = new File(ClassLoader.getSystemResource(
					"testcases")
					.getPath());
		}
		File folder = FILE_FOLDER.listFiles(getFileFilter(project))[0];
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
	 * @param className The name of the class.
	 * @param feature The feature containing the error
	 * @param javaLine The line at the generated java file
	 * @param composedLine The line at the composed jak file
	 * @param jakLine The line at the source file
	 */
	private void test(String className, String feature, int javaLine, int composedLine, int jakLine) {
		int composedJakLine = calculateComposedJakLine(javaLine, className + ".javaX");
		if (composedLine != composedJakLine) {
			System.out.println("Wrong composed line @ " + className + ".java (expected: " + composedLine +
					" but was: " + composedJakLine + ")");
		}
		
		String content = readFile(getFile(className + ".jak"));
		int line = event.setSourceFile(content, composedJakLine); 

		if (!event.fileName.equals("../features/" + feature + "/" + className + ".jak")) {
			System.out.println("Wrong source files @ " + className + ".java (expected: " + "../features/" + feature + "/" + className + ".jak" +
					" but was: " + event.fileName + ")");
		}
		
		int sourceLine = event.setSourceLine(composedJakLine, line, readFile(getFile(feature + "_" + className + ".jak")));
		if (jakLine != sourceLine) {
			System.out.println("Wrong source line @ " + className + ".java (expected: " + jakLine +
					" but was: " + sourceLine + ")");
		}
		// TODO AHEAD error propagation add this test
		//assertEquals(jakLine, sourceLine);
	}
	
	private int calculateComposedJakLine(int javaLine, String fileName) {
		return event.calculateComposedJakLine(javaLine, readFile(getFile(fileName)));
	}

	private String readFile(File file) {
		Scanner scanner = null;
		StringBuilder builder = new StringBuilder();
		try {
			scanner = new Scanner(file);
			while (scanner.hasNext()) {
				builder.append(scanner.nextLine());
				builder.append("\r\n");
			}
		} catch (FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if(scanner!=null)scanner.close();
		}
		return builder.toString();
	}

	/*°**********************************************************************
	 * project		 : HelloWorld-AHEAD										*
	 * class  		 : Main													*
	 * configuration : BeatifulWorld										*
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
	
	/*°**********************************************************************
	 * project		 : DesktopSearcher-AHEAD								*
	 * class  		 : MainFrame											*
	 * configuration : config												*
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