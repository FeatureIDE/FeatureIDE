/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io;

import static org.junit.Assert.*;
import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslReader;

/**
 * Basic test super-class for IFeatureModelReader/IFeatureModelWriter
 * implementations tests will write feature-models into a string and read it
 * back to check if the result is as expected
 * 
 * To add additional readers/writers extend this class and override abstract
 * methods
 * 
 * Add model.m files into folder testFeatureModels to add test cases
 * 
 * @author Fabian Benduhn
 */
@RunWith(Parameterized.class)
public abstract class TAbstractFeatureModelReaderWriter {

	// featuremodels are created by using GuidslWriter, so for each test case
	// there should be an corresponding test case for the
	// GuidslReader which tests the resulting FeatureModel directly

	// TODO replace MODEL_FILE_PATH by something that works on both:
	// build-server and offline in
	// workspace
	// For now: uncomment this to run tests in workspace:
//	protected static String sep = System.getProperty("file.separator");
//	protected static File MODEL_FILE_PATH = new File("src" + sep
//			+ "testFeatureModels" + sep);
	 protected static File MODEL_FILE_PATH = new
	 File("/vol1/teamcity_itidb/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/testFeatureModels/");

	FeatureModel origFm;
	FeatureModel newFm;
	String failureMessage;

	public TAbstractFeatureModelReaderWriter(FeatureModel fm, String s)
			throws UnsupportedModelException {
		this.origFm = fm;
		this.newFm = writeAndReadModel();
		this.failureMessage = "(" + s + ")";
	}

	@Parameters
	public static Collection<Object[]> getModels()
			throws FileNotFoundException, UnsupportedModelException {
		Collection<Object[]> params = new ArrayList<Object[]>();
		for (File f : MODEL_FILE_PATH.listFiles(getFileFilter(".m"))) {
			Object[] models = new Object[2];

			FeatureModel fm = new FeatureModel();
			GuidslReader r = new GuidslReader(fm);
			r.readFromFile(f);
			models[0] = fm;
			models[1] = f.getName();
			params.add(models);

		}

		return params;
	}

	@Test
	public void testRoot() throws FileNotFoundException,
			UnsupportedModelException {

		assertEquals(failureMessage, origFm.getRoot().getName(), newFm
				.getRoot().getName());
	}

	@Test
	public void testFeatureCount() throws FileNotFoundException,
			UnsupportedModelException {

		assertEquals(failureMessage, origFm.getFeatures().size(), newFm
				.getFeatures().size());
	}

	@Test
	public void testFeatureNames() throws FileNotFoundException,
			UnsupportedModelException {

		assertEquals(failureMessage, origFm.getFeatureNames(),
				newFm.getFeatureNames());
	}

	@Test
	public void testFeatureGroupTypeAnd() throws FileNotFoundException,
			UnsupportedModelException {
		for (Feature origF : origFm.getFeatures()) {

			if (origF.isAnd()) {
				Feature newF = newFm.getFeature(origF.getName());
				if (newF == null)
					fail("Feature " + origF.getName() + " cannot be found");
				else {
					assertTrue(failureMessage, newFm
							.getFeature(origF.getName()).isAnd());
				}
			}
		}
	}

	@Test
	public void testFeatureGroupTypeOr() throws FileNotFoundException,
			UnsupportedModelException {
		for (Feature origF : origFm.getFeatures()) {

			if (origF.isOr()) {
				Feature newF = newFm.getFeature(origF.getName());
				if (newF == null)
					fail("Feature " + origF.getName() + " cannot be found");
				else {
					assertTrue(failureMessage, newFm
							.getFeature(origF.getName()).isOr());
				}
			}
		}
	}

	@Test
	public void testFeatureGroupTypeAlternative() throws FileNotFoundException,
			UnsupportedModelException {
		for (Feature origF : origFm.getFeatures()) {

			if (origF.isAlternative()) {
				Feature newF = newFm.getFeature(origF.getName());
				if (newF == null)
					fail("Feature " + origF.getName() + " cannot be found");
				else {
					assertTrue(failureMessage, newFm
							.getFeature(origF.getName()).isAlternative());
				}
			}
		}
	}

	@Test
	public void testFeatureConcrete() throws FileNotFoundException,
			UnsupportedModelException {
		for (Feature origF : origFm.getFeatures()) {

			if (origF.isConcrete()) {
				Feature newF = newFm.getFeature(origF.getName());
				if (newF == null)
					fail("Feature " + origF.getName() + " cannot be found");
				else {
					assertTrue(failureMessage, newFm
							.getFeature(origF.getName()).isConcrete());
				}
			}
		}
	}

	@Test
	public void testFeatureHidden() throws FileNotFoundException,
			UnsupportedModelException {
		for (Feature origF : origFm.getFeatures()) {

			if (origF.isHidden()) {
				Feature newF = newFm.getFeature(origF.getName());
				if (newF == null)
					fail("Feature " + origF.getName() + " cannot be found");
				else {
					assertTrue(failureMessage, newFm
							.getFeature(origF.getName()).isHidden());
				}
			}
		}
	}

	@Test
	public void testFeatureMandatory() throws FileNotFoundException,
			UnsupportedModelException {
		for (Feature origF : origFm.getFeatures()) {

			if (origF.isMandatory()) {
				Feature newF = newFm.getFeature(origF.getName());
				if (newF == null)
					fail("Feature " + origF.getName() + " cannot be found");
				else {
					assertTrue(failureMessage, newFm
							.getFeature(origF.getName()).isMandatory());
				}
			}
		}
	}

	@Test
	public void testPropNodes() throws FileNotFoundException,
			UnsupportedModelException {
		assertEquals(failureMessage, origFm.getPropositionalNodes(),
				newFm.getPropositionalNodes());
	}

	@Test
	public void testConstraintCount() throws FileNotFoundException,
			UnsupportedModelException {
		assertEquals(failureMessage, origFm.getConstraintCount(),
				origFm.getConstraintCount());
	}

	@Test
	public void testConstraints() throws FileNotFoundException,
			UnsupportedModelException {
		assertEquals(failureMessage, origFm.getConstraints(),
				origFm.getConstraints());
	}

	@Test
	public void testAnnotations() throws FileNotFoundException,
			UnsupportedModelException {
		assertEquals(failureMessage, origFm.getAnnotations(),
				origFm.getAnnotations());
	}

	@Test
	public void testIsRefactoring() throws FileNotFoundException,
			UnsupportedModelException {

		ModelComparator mc = new ModelComparator(1000);

		assertTrue(failureMessage,
				mc.compare(origFm, newFm).equals(Comparison.REFACTORING));
	}

	private final FeatureModel writeAndReadModel()
			throws UnsupportedModelException {
		FeatureModel newFm = new FeatureModel();
		IFeatureModelWriter writer = getWriter(origFm);
		IFeatureModelReader reader = getReader(newFm);
		reader.readFromString(writer.writeToString());
		return newFm;

	}

	private final static FileFilter getFileFilter(final String s) {
		FileFilter filter = new FileFilter() {

			@Override
			public boolean accept(File pathname) {

				if (pathname.getName().endsWith(s)) {

					return true;
				} else {

					return false;
				}
			}
		};
		return filter;
	}

	protected abstract IFeatureModelWriter getWriter(FeatureModel fm);

	protected abstract IFeatureModelReader getReader(FeatureModel fm);

}
