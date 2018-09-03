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
package de.ovgu.featureide.fm.ui.editors;

import static org.junit.Assert.assertEquals;

import java.io.IOException;
import java.nio.file.Paths;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.configuration.LatexFormat;

/**
 * This class test the LaTeX-Export for the configuration files.
 *
 * @author Simon Wenk
 * @author Yang Liu
 */
public class LatexFormatTest {

	private static final String TEST_LATEX_FILES_PATH = "testLatexFiles/ConfigurationTest/";
	private static final String TEST_XML_FILE_NAME = "testFeatureModels/TestConfiguration.xml";
	private static final String TEST_XML_MODEL_FILE_NAME = "TestConfigurationModel.xml";
	private static final String TEST_TEX_MAIN_FILE_NAME = "ConfigurationTest.tex";
	private static final String TEST_TEX_HEAD_FILE_NAME = "head.tex";
	private static final String TEST_TEX_BODY_FILE_NAME = "body.tex";

	@Test
	public void testLatexExporter() {
		final IFeatureModel modelExample = Commons.loadTestFeatureModelFromFile(TEST_XML_MODEL_FILE_NAME);
		final Configuration configExample = new Configuration(modelExample, false);
		final IPersistentFormat<Configuration> formatHead = new LatexFormat.LaTeXHead();
		final IPersistentFormat<Configuration> formatMain = new LatexFormat.LaTeXMain();
		final IPersistentFormat<Configuration> formatBody = new LatexFormat.LaTeXBody(TEST_TEX_MAIN_FILE_NAME);
		String head = new String();
		String main = new String();
		String body = new String();
		String testHead = new String();
		String testBody = new String();
		String testMain = new String();

		// load example files
		try {
			testHead = FileSystem.readtoString(Paths.get(Commons.getRemoteOrLocalFolder(TEST_LATEX_FILES_PATH).getPath()).resolve(TEST_TEX_HEAD_FILE_NAME));
		} catch (final IOException e) {
			FMUIPlugin.getDefault().logError(e);
		}

		try {
			testBody = FileSystem.readtoString(Paths.get(Commons.getRemoteOrLocalFolder(TEST_LATEX_FILES_PATH).getPath()).resolve(TEST_TEX_BODY_FILE_NAME));
		} catch (final IOException e) {
			FMUIPlugin.getDefault().logError(e);
		}

		try {
			testMain = FileSystem.readtoString(Paths.get(Commons.getRemoteOrLocalFolder(TEST_LATEX_FILES_PATH).getPath()).resolve(TEST_TEX_MAIN_FILE_NAME));
		} catch (final IOException e) {
			FMUIPlugin.getDefault().logError(e);
		}

		// initiate Model
		FileHandler.load(Paths.get(Commons.getRemoteOrLocalFolder(TEST_XML_FILE_NAME).toURI()), configExample, ConfigFormatManager.getInstance());

		// execute LaTeXExporter
		head = formatHead.write(configExample).replace(System.lineSeparator(), "\n");
		main = formatMain.write(configExample).replace(System.lineSeparator(), "\n");
		body = formatBody.write(configExample).replace(System.lineSeparator(), "\n");

		// test the Tikz-Exporter
		assertEquals(testHead, head);
		assertEquals(testMain, main);
		assertEquals(testBody, body);
	}

}
