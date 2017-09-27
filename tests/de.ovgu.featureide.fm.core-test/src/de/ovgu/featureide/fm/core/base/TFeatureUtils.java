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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.base;

import static org.junit.Assert.assertTrue;

import org.junit.Assert;
import org.junit.Test;

import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * Test class for {@link FeatureUtils}
 *
 * @author Jens Meinicke
 */
public class TFeatureUtils {

	final static IFeatureModelFactory FACTORY = FMFactoryManager.getDefaultFactory();

	/**
	 * Test method for {@link de.ovgu.featureide.fm.core.base.FeatureUtils#getParent(de.ovgu.featureide.fm.core.base.IFeature)}.
	 */
	@Test
	public void testGetParent() {
		final IFeatureModel model = FACTORY.createFeatureModel();
		final IFeature featureA = FACTORY.createFeature(model, "A");
		model.addFeature(featureA);
		model.getStructure().setRoot(featureA.getStructure());

		final IFeature featureB = FACTORY.createFeature(model, "B");
		model.addFeature(featureB);

		featureA.getStructure().addChild(featureB.getStructure());

		IFeature parent = FeatureUtils.getParent(featureB);
		assertTrue(parent == featureA);

		parent = FeatureUtils.getParent(featureA);
		Assert.assertNull(parent);

		parent = FeatureUtils.getParent(null);
		Assert.assertNull(parent);
	}

}
