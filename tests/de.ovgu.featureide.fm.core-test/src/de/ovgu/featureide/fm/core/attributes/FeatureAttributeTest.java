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
package de.ovgu.featureide.fm.core.attributes;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * TODO description
 *
 * @author Joshua
 */
public class FeatureAttributeTest {

	private static final String MODEL_NAME = "featureAttributes.xml";

	private static final String FEATURE_HELLO = "HelloWorld";
	private static final String FEATURE_FEATURE = "Feature";
	private static final String FEATURE_WONDERFUL = "Wonderful";
	private static final String FEATURE_BEAUTIFUL = "Beautiful";
	private static final String FEATURE_WORLD = "World";
	private static final IFeatureModelFactory factory = FMFactoryManager.getDefaultFactory();

	@Test
	public void countFeatureAttributes() {
		final IFeatureModel fm = Commons.loadTestFeatureModelFromFile(MODEL_NAME);

		for (final IFeature feature : fm.getFeatures()) {
			if (feature.getName().equals(FEATURE_HELLO)) {
				assertEquals(1, feature.getProperty().getAttributes().size());
			}
			if (feature.getName().equals(FEATURE_FEATURE)) {
				assertEquals(1, feature.getProperty().getAttributes().size());
			}
			if (feature.getName().equals(FEATURE_WONDERFUL)) {
				assertEquals(0, feature.getProperty().getAttributes().size());
			}
			if (feature.getName().equals(FEATURE_BEAUTIFUL)) {
				assertEquals(2, feature.getProperty().getAttributes().size());
			}
			if (feature.getName().equals(FEATURE_WORLD)) {
				assertEquals(0, feature.getProperty().getAttributes().size());
			}
		}
	}
}
