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
package de.ovgu.featureide.featurehouse.meta;

import de.ovgu.featureide.featurehouse.meta.featuremodel.FeatureModelClassGenerator;

/**
 * Test for {@link FeatureModelClassGenerator}.
 *
 * @author Jens Meinicke
 */
public class FeatureModelClassGeneratorTest {

//	@Test
//	public void testMetaJPF() {
//		IFeatureModel model = init("model.xml");
//		System.out.println();
//		System.out.println("------------------------- Start Test JPF  ---------------------");
//		System.out.println();
//		new FeatureModelClassGenerator(model, IFeatureProject.META_MODEL_CHECKING);
//		System.out.println();
//		System.out.println("------------------------- End Test JPF  ---------------------");
//		System.out.println();
//	}
//
//	@Test
//	public void testMetaKeY() {
//		System.out.println();
//		System.out.println("------------------------- Start Test KEY  ---------------------");
//		System.out.println();
//		IFeatureModel model = init("model.xml");
//		new FeatureModelClassGenerator(model, IFeatureProject.META_THEOREM_PROVING);
//		System.out.println();
//		System.out.println("------------------------- End Test KEY  ---------------------");
//		System.out.println();
//	}
//
//	@Test
//	public void testMetaBDD() {
//		System.out.println();
//		System.out.println("------------------------- Start Test BDD  ---------------------");
//		System.out.println();
//		IFeatureModel model = init("model.xml");
//		new FeatureModelClassGenerator(model, IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML);
//		System.out.println();
//		System.out.println("------------------------- End Test BDD  ---------------------");
//		System.out.println();
//	}
//
//	@Test
//	public void testMetaVarexJ() {
//		System.out.println();
//		System.out.println("------------------------- Start Test VarexJ  ---------------------");
//		System.out.println();
//		IFeatureModel model = init("model.xml");
//		new FeatureModelClassGenerator(model, IFeatureProject.META_VAREXJ);
//		System.out.println();
//		System.out.println("------------------------- End Test VarexJ  ---------------------");
//		System.out.println();
//	}
//
//	protected static File MODEL_FILE_FOLDER = getFolder();
//
//	private static final FileFilter filter = new FileFilter() {
//		@Override
//		public boolean accept(File pathname) {
//			return pathname.getName().endsWith(".xml");
//		}
//	};
//
//	private static File getFolder() {
//		File folder =  new File("/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.core.featurehouse-test/src/metafeaturemodels/");
//		if (!folder.canRead()) {
//			folder =  new File(ClassLoader.getSystemResource("metafeaturemodels").getPath());
//		}
//		return folder;
//	}
//
//	private final IFeatureModel init(String name) {
//		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
//
//		for (File f : MODEL_FILE_FOLDER.listFiles(filter)) {
//			if (f.getName().equals(name)) {
//				try {
//					new XmlFeatureModelReader(fm).readFromFile(f);
//					break;
//				} catch (FileNotFoundException e) {
//					e.printStackTrace();
//				} catch (UnsupportedModelException e) {
//					e.printStackTrace();
//				}
//			}
//		}
//		return fm;
//	}

}
