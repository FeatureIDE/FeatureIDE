package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static org.junit.Assert.assertEquals;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.Test;

public class StatisticProgramSizeNewTest {

	private final static String getContent(final String name) {
		StringBuilder content = new StringBuilder();
		File fileFolder = getFolder();
		for (File f : fileFolder.listFiles()) {
			if (f.getName().equals(name)) {
				String s;
				try (FileReader fr = new FileReader(f.getPath().toString());BufferedReader br = new BufferedReader(fr)) {
					while ((s = br.readLine()) != null) {
						content.append(s + "\n");
					}
				} catch (IOException e) {
					e.printStackTrace();
				}

				break;
			}
		}
		return content.toString();
	}

	private static File getFolder() {
		File folder = new File("/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.ui-test/src/statisticsfiles/");
		if (!folder.canRead()) {
			folder = new File(ClassLoader.getSystemResource("statisticsfiles").getPath());
		}
		return folder;
	}

	@Test
	public void testGraph() throws Exception {
		BufferedReader br = new BufferedReader(new StringReader(getContent("Graph.jak")));
		assertEquals(37, StatisticsProgramSizeNew.countLineNumber("//", "/*", "*/", br));
	}
	
	@Test
	public void testDaily() throws Exception {
		BufferedReader br = new BufferedReader(new StringReader(getContent("Daily.jak")));
		assertEquals(34, StatisticsProgramSizeNew.countLineNumber("//", "/*", "*/", br));
	}
	

}