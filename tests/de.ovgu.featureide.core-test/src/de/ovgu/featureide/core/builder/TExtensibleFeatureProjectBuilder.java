package de.ovgu.featureide.core.builder;


import static org.junit.Assert.*;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import de.ovgu.featureide.core.builder.ExtensibleFeatureProjectBuilder;

/**
 * 
 * 
 * @author Fabian Benduhn
 */
public class TExtensibleFeatureProjectBuilder {
	@Rule
	public TemporaryFolder testFolder = new TemporaryFolder();

	@Test
	public void TestGetSelectedFeatures() throws IOException {
		ArrayList<String> expectedList = new ArrayList<String>();
		expectedList.add("one");
		expectedList.add("two");
		expectedList.add("three");

		File tempFile = testFolder.newFile("file.txt");

		FileWriter fw = new FileWriter(tempFile);
		fw.write("one   two \n three");
		fw.close();
		ArrayList<String> list = ExtensibleFeatureProjectBuilder
				.getTokenListFromFile(tempFile);
		assertEquals(expectedList, list);
	}

}
