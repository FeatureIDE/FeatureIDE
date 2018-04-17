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
package de.ovgu.featureide.fm.core.io;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * Basic test super-class for IFeatureModelReader/IFeatureModelWriter implementations tests will write feature-models into a string and read it back to check if
 * the result is as expected
 *
 * To add additional readers/writers extend this class and override abstract methods
 *
 * Add model.m files into folder testFeatureModels to add test cases
 *
 * @author Fabian Benduhn
 */
@RunWith(Parameterized.class)
public abstract class TAbstractFeatureModelReaderWriter {

	// feature models are created by using XmlFeatureModelWriter, so for each
	// test case
	// there should be an corresponding test case for the
	// GuidslReader which tests the resulting FeatureModel directly

	protected static File MODEL_FILE_FOLDER = Commons.getRemoteOrLocalFolder("testFeatureModels/");

	static boolean online = false;
	protected IFeatureModel origFm;
	protected IFeatureModel newFm;
	protected String failureMessage;

	public TAbstractFeatureModelReaderWriter(IFeatureModel fm, String s) {
		origFm = fm;
		try {
			newFm = writeAndReadModel();
		} catch (final UnsupportedModelException e) {
			fail();
		}
		failureMessage = "(" + s + ")";
	}

	@Parameters
	public static Collection<Object[]> getModels() throws FileNotFoundException, UnsupportedModelException {
		// first tries the location on build server, if this fails tries to use local location
		if (!MODEL_FILE_FOLDER.canRead()) {
			MODEL_FILE_FOLDER = new File(ClassLoader.getSystemResource("testFeatureModels").getPath());
		}
		final Collection<Object[]> params = new ArrayList<Object[]>();
		final FileFilter fileFilter = getFileFilter(".xml");
		if (fileFilter == null) {
			throw new RuntimeException();
		}

		for (final File f : MODEL_FILE_FOLDER.listFiles(fileFilter)) {
			final Object[] models = new Object[2];
			final IFeatureModel fm = FeatureModelManager.load(f.toPath()).getObject();
			models[0] = fm;
			models[1] = f.getName();
			params.add(models);

		}

		return params;
	}

	@Test
	public void testRoot() throws FileNotFoundException, UnsupportedModelException {
		assertEquals(failureMessage, origFm.getStructure().getRoot().getFeature().getName(), newFm.getStructure().getRoot().getFeature().getName());
	}

	@Test
	public void testFeatureCount() throws FileNotFoundException, UnsupportedModelException {
		final Collection<IFeature> originalFeatures = Functional.toList(origFm.getFeatures());
		final Collection<IFeature> newFeatures = Functional.toList(newFm.getFeatures());
		assertEquals(failureMessage, originalFeatures.size(), newFeatures.size());
	}

	@Test
	public void testFeatureNames() throws FileNotFoundException, UnsupportedModelException {
		assertTrue(failureMessage, Functional.equals(origFm.getFeatures(), newFm.getFeatures(), FeatureUtils.GET_FEATURE_NAME));
	}

	@Test
	public void testFeatureGroupTypeAnd() throws FileNotFoundException, UnsupportedModelException {
		for (final IFeature origF : origFm.getFeatures()) {
			if (origF.getStructure().isAnd()) {
				final IFeature newF = newFm.getFeature(origF.getName());
				if (newF == null) {
					// fail("Feature " + origF.getName() + " cannot be found");
				} else {
					assertTrue(failureMessage, newFm.getFeature(origF.getName()).getStructure().isAnd());
				}
			}
		}
	}

	@Test
	public void testFeatureGroupTypeOr() throws FileNotFoundException, UnsupportedModelException {
		for (final IFeature origF : origFm.getFeatures()) {
			if (origF.getStructure().isOr()) {
				final IFeature newF = newFm.getFeature(origF.getName());
//				System.out.println("origF:[" + origF.getStructure().isOr() + "]" + origF + "\nnewF:[" + newF.getStructure().isOr() + "]"
//						+ newF + "\n: ");
				assertTrue(failureMessage, newF.getStructure().isOr());
			}
		}
	}

	@Test
	public void testFeatureGroupTypeAlternative() throws FileNotFoundException, UnsupportedModelException {
		for (final IFeature origF : origFm.getFeatures()) {
			if (origF.getStructure().isAlternative()) {
				final IFeature newF = newFm.getFeature(origF.getName());
				assertTrue(failureMessage, newF.getStructure().isAlternative());
			}
		}
	}

	@Test
	public void testFeatureConcrete() throws FileNotFoundException, UnsupportedModelException {
		for (final IFeature origF : origFm.getFeatures()) {
			if (origF.getStructure().isConcrete()) {
				final IFeature newF = newFm.getFeature(origF.getName());
				if (newF == null) {
					// fail("Feature " + origF.getName() + " cannot be found");
				} else {
					assertTrue(failureMessage + origF, newFm.getFeature(origF.getName()).getStructure().isConcrete());
				}
			}
		}
	}

	@Test
	public void testFeatureHidden() throws FileNotFoundException, UnsupportedModelException {
		for (final IFeature origF : origFm.getFeatures()) {

			if (origF.getStructure().isHidden()) {
				final IFeature newF = newFm.getFeature(origF.getName());
				if (newF == null) {
					// fail("Feature " + origF.getName() + " cannot be found");
				} else {
					assertEquals(failureMessage + "Feature: " + origF.getName(), origF.getStructure().isHidden(),
							newFm.getFeature(origF.getName()).getStructure().isHidden());
				}
			}
		}
	}

	@Test
	public void testFeatureMandatory() throws FileNotFoundException, UnsupportedModelException {
		for (final IFeature origF : origFm.getFeatures()) {

			if (origF.getStructure().isMandatory()) {
				final IFeature newF = newFm.getFeature(origF.getName());
				if (newF == null) {
					// fail("Feature " + origF.getName() + " cannot be found");
				} else {
					assertTrue(failureMessage, newFm.getFeature(origF.getName()).getStructure().isMandatory());
				}
			}
		}
	}

	// TODO @Fabian @Test
	public void testPropNodes() throws FileNotFoundException, UnsupportedModelException {
		for (final IConstraint constraint : origFm.getConstraints()) {
			assertFalse(failureMessage + constraint, newFm.getConstraints().contains(constraint));
		}
	}

	@Test
	public void testConstraintCount() throws FileNotFoundException, UnsupportedModelException {
		assertEquals(failureMessage, origFm.getConstraintCount(), newFm.getConstraintCount());
	}

	@Test
	public void testConstraints() throws FileNotFoundException, UnsupportedModelException {
		assertEquals(failureMessage, origFm.getConstraints().toString(), newFm.getConstraints().toString());
	}

	@Test
	public void testAnnotations() throws FileNotFoundException, UnsupportedModelException {
		assertEquals(failureMessage, origFm.getProperty().getAnnotations(), newFm.getProperty().getAnnotations());
	}

	// @Test // java.lang.AssertionError: (gpl_medium_model.xml) expected:<REFACTORING> but was:<SPECIALIZATION>
	public void testIsRefactoring() throws FileNotFoundException, UnsupportedModelException {
		final Comparison compare = new ModelComparator(1000).compare(origFm, newFm);
		if (!compare.equals(Comparison.ARBITRARY)) {
			assertEquals(failureMessage, Comparison.REFACTORING, compare);
		}

	}

	@Test
	public void testDescription() {
		for (final IFeature origFeature : origFm.getFeatures()) {
			final IFeature newFeature = newFm.getFeature(origFeature.getName());
			assertEquals(origFeature.getProperty().getDescription(), newFeature.getProperty().getDescription());
		}
	}

	private final IFeatureModel writeAndReadModel() throws UnsupportedModelException {
		IFeatureModel newFm = null;
		try {
			newFm = FMFactoryManager.getDefaultFactoryForPath(origFm.getFactoryID()).createFeatureModel();
		} catch (final NoSuchExtensionException e) {
			fail();
		}
		final IFeatureModelFormat format = getFormat();
		final String write = format.getInstance().write(origFm);
		format.getInstance().read(newFm, write);
		return newFm;
	}

	private final static FileFilter getFileFilter(final String s) {
		final FileFilter filter = new FileFilter() {

			@Override
			public boolean accept(File pathname) {
				return pathname.getName().endsWith(s);
			}
		};
		return filter;
	}

	protected abstract IFeatureModelFormat getFormat();

}
