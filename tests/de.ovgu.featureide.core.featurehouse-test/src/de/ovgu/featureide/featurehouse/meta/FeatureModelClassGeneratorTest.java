/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse.meta;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * TODO description
 * 
 * @author Jens Meinicke
 */
public class FeatureModelClassGeneratorTest {

//	@Test
	public void testMetaJPF() {
		FeatureModel model = init("model.xml");
		System.out.println(new FeatureModelClassGenerator(model, false).getStringBuilder());
	}
	
//	@Test
	public void testMetaKeY() {
		FeatureModel model = init("model.xml");
		System.out.println(new FeatureModelClassGenerator(model, true).getStringBuilder());
	}
	
	protected static File MODEL_FILE_FOLDER = getFolder();
	
	private static final FileFilter filter = new FileFilter() {
		@Override
		public boolean accept(File pathname) {
			return pathname.getName().endsWith(".xml");
		}
	};
	
	private static File getFolder() { 
		File folder =  new File("/vol1/teamcity_itidb/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.core.featurehouse-test/src/metafeaturemodels/"); 
		if (!folder.canRead()) { 
			folder =  new File(ClassLoader.getSystemResource("metafeaturemodels").getPath()); 
		}
		return folder; 
	}
	
	private final FeatureModel init(String name) {
		FeatureModel fm = new FeatureModel();
		for (File f : MODEL_FILE_FOLDER.listFiles(filter)) {
			if (f.getName().equals(name)) {
				try {
					new XmlFeatureModelReader(fm).readFromFile(f);
					break;
				} catch (FileNotFoundException e) {
					e.printStackTrace();
				} catch (UnsupportedModelException e) {
					e.printStackTrace();
				}
			}
		}
		return fm;
	}

}
