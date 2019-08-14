/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.outlineentry.AttributeMaximumEntry;
import de.ovgu.featureide.fm.attributes.outlineentry.AttributeMinimumEntry;
import de.ovgu.featureide.fm.attributes.outlineentry.CountAttributeComputation;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;

public class TExtendedOutline {

	@Before
	public void prepareWorkbench() {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
	}

	@Test
	public void testMaximumEstimationComputationDouble() {
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		Configuration congf = new Configuration(new FeatureModelFormula(model));

		for (final SelectableFeature f : congf.getFeatures()) {
			if (f.getFeature().getName().equals("Full Grain ")) {
				congf.setManual(f, Selection.SELECTED);
			}
		}

		// Get attribute to compute
		ExtendedFeature feature = (ExtendedFeature) model.getStructure().getRoot().getFeature();
		IFeatureAttribute attributePrice = null;
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.getName().equals("Price")) {
				attributePrice = att;
			}
		}

		assertTrue(attributePrice != null);

		// maximum
		AttributeMaximumEntry max = new AttributeMaximumEntry(congf, attributePrice);
		Object valueObject = max.getResult();

		assertTrue(valueObject instanceof Double);
		double value = (double) valueObject;
		assertTrue(value == 8.7d);
	}

	@Test
	public void testMinimumEstimationComputationDouble() {
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		Configuration congf = new Configuration(new FeatureModelFormula(model));

		for (final SelectableFeature f : congf.getFeatures()) {
			if (f.getFeature().getName().equals("Full Grain ")) {
				congf.setManual(f, Selection.SELECTED);
			}
		}

		// Get attribute to compute
		ExtendedFeature feature = (ExtendedFeature) model.getStructure().getRoot().getFeature();
		IFeatureAttribute attributePrice = null;
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.getName().equals("Price")) {
				attributePrice = att;
			}
		}

		assertTrue(attributePrice != null);

		// maximum
		AttributeMinimumEntry max = new AttributeMinimumEntry(congf, attributePrice);
		Object valueObject = max.getResult();

		assertTrue(valueObject instanceof Double);
		double value = (double) valueObject;
		assertTrue(value == 1.99d);
	}

	@Test
	public void testCountAttributeComputation() {
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		Configuration congf = new Configuration(new FeatureModelFormula(model));

		for (final SelectableFeature f : congf.getFeatures()) {
			if (f.getFeature().getName().equals("Full Grain ")) {
				congf.setManual(f, Selection.SELECTED);
			}
		}

		// Get attribute to compute
		ExtendedFeature feature = (ExtendedFeature) model.getStructure().getRoot().getFeature();
		IFeatureAttribute attributePrice = null;
		for (IFeatureAttribute att : feature.getAttributes()) {
			if (att.getName().equals("Price")) {
				attributePrice = att;
			}
		}

		assertTrue(attributePrice != null);

		// maximum
		CountAttributeComputation max = new CountAttributeComputation(congf, attributePrice);
		Object valueObject = max.calculateCount();

		assertTrue(valueObject instanceof Integer);
		int value = (int) valueObject;
		assertTrue(value == 19);
	}
}
