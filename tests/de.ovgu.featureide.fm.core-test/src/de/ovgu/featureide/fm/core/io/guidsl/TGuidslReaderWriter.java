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
package de.ovgu.featureide.fm.core.io.guidsl;

import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Test class for GuidslReader
 *
 * @author Fabian Benduhn
 */
public class TGuidslReaderWriter extends TAbstractFeatureModelReaderWriter {

	/**
	 * @param file
	 * @throws UnsupportedModelException
	 */
	public TGuidslReaderWriter(IFeatureModel fm, String s) throws UnsupportedModelException {
		super(fm, s);
	}

	@Override
	protected IFeatureModelFormat getFormat() {
		return new GuidslFormat();
	}

	// guidsl does not save concrete compound features
	@Override
	public void testFeatureConcrete() {
		for (final IFeature origF : origFm.getFeatures()) {
			if (!origF.getStructure().isConcrete() && origF.getStructure().isConcrete()) {
				final IFeature newF = newFm.getFeature(origF.getName());
				if (newF == null) {
					// fail("Feature " + origF.getName() + " cannot be found");
				} else {
					assertTrue(failureMessage + origF, newFm.getFeature(origF.getName()).getStructure().isConcrete());
				}
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.TAbstractFeatureModelReaderWriter#testConstraintCount()
	 */
	@Override
	public void testConstraintCount() throws FileNotFoundException, UnsupportedModelException {}

	@Override
	public void testDescription() {
		// description not implemented
	}

}
