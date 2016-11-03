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
package de.ovgu.featureide.fm.core.configuration;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileFilter;
import java.io.InputStream;

import org.junit.Test;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * Test class for the {@link ConfigurationReader}.
 * 
 * @author Stefan Krueger
 * @author Florian Proksch
 */
public class TConfigurationReader {

	private static final String FEATUREMODEL_PATH = "/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/analyzefeaturemodels/";

	protected static File MODEL_FILE_FOLDER = getFolder();

	private static final FileFilter filter = new FileFilter() {
		@Override
		public boolean accept(File pathname) {
			return pathname.getName().endsWith(".xml");
		}
	};

	String text = "";
	InputStream a; // = new InputStream(text.getBytes(Charset.availableCharsets().get("UTF-8")));

	private IFeatureModel FM_test_1 = init("test_5.xml");

	private static File getFolder() {
		File folder = new File(FEATUREMODEL_PATH);
		if (!folder.canRead()) {
			folder = new File(ClassLoader.getSystemResource("analyzefeaturemodels").getPath());
		}
		return folder;
	}

	private final IFeatureModel init(String name) {
		IFeatureModel fm = null;
		File[] listFiles = MODEL_FILE_FOLDER.listFiles(filter);
		assertNotNull(listFiles);
		for (File f : listFiles) {
			if (f.getName().equals(name)) {
				fm = FeatureModelManager.readFromFile(f.toPath());
				if (fm != null) {
					break;
				}
			}
		}
		return fm;
	}

	@Test
	public void isValidConfiguration() {
		final Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "C#");

		assertFalse(c.isValid());
	}

	@Test
	public void isValidConfiguration2() {
		Configuration c = new Configuration(FM_test_1, false);
		c.setManual("C#", Selection.SELECTED);
		c.setManual("Python Ruby", Selection.SELECTED);
		c.setManual("Bash   script   ", Selection.UNSELECTED);
		c.setManual("C++", Selection.SELECTED);
		assertFalse(c.isValid());
	}

	@Test
	public void isValidConfiguration3() {
		Configuration c = new Configuration(FM_test_1, true);
		c.setManual("C#", Selection.SELECTED);
		c.setManual("Python Ruby", Selection.SELECTED);
		c.setManual("Bash   script   ", Selection.SELECTED);
		c.setManual("C++", Selection.SELECTED);
		assertTrue(c.isValid());
	}

	@Test
	public void isValidConfiguration4() {
		Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "C# \njute \n \"Bash   script   \"");
		assertFalse(c.isValid());
	}

	@Test
	public void isValidConfiguration5() {
		Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "C# \njute \n \"Bash   script   \" \"Python Ruby\"");
		assertTrue(c.isValid());
	}

	@Test
	public void isValidConfiguration6() {
		Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "C# \njute \n \"Bash   script   \" \n\"Python Ruby\" \n\"C++\"");
		assertTrue(c.isValid());
	}

	@Test
	public void isValidConfiguration7() {
		Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "C# \njute \n \"Bash   script    \n\"Python Ruby\" \n\"C++\"");
		assertFalse(c.isValid());
	}

	@Test
	public void isValidConfiguration8() {
		Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "C# \nj ute \n \"Bash   script    \"\n\"Python Ruby\" \n\"C++\"");
		assertFalse(c.isValid());
	}

	@Test
	public void isValidConfiguration9() {
		Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "C# \njute \n \"Bash   script   \" Python Ruby\" \n\"C++\"");
		assertFalse(c.isValid());
	}

	@Test
	public void isValidConfiguration10() {
		Configuration c = new Configuration(FM_test_1, false);
		final DefaultFormat r = new DefaultFormat();
		r.read(c, "jute \"Bash   script   \" \"Python C# Ruby\" \"C++\"");
		assertTrue(c.isValid());
	}
}
