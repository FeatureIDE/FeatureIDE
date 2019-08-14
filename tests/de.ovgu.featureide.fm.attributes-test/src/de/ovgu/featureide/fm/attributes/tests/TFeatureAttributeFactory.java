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

import org.junit.Test;

import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeFactory;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;

public class TFeatureAttributeFactory {

	private static final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();

	/**
	 * Tests the creation of the different types of attributes.
	 * 
	 * @result The different attributes should contain the assigned information and should be of the correct type.
	 */
	@Test
	public void test_AttributeInit() {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
		ExtendedFeatureModel model = Commons.getBaseModel();
		ExtendedFeature root = (ExtendedFeature) model.getFeature("Root");

		// Create all types of attributes with values
		IFeatureAttribute stringAttribute = attributeFactory.createStringAttribute(root, "stringTest", "EMPTY", "Ein Test", false, false);
		IFeatureAttribute booleanAttribute = attributeFactory.createBooleanAttribute(root, "booleanTest", "State", true, true, false);
		IFeatureAttribute longAttribute = attributeFactory.createLongAttribute(root, "longTest", "Euro", Long.MAX_VALUE, false, true);
		IFeatureAttribute doubleAttribute = attributeFactory.createDoubleAttribute(root, "doubleTest", "Dollar", Double.MAX_VALUE, true, true);

		// Create all types of attributes with null values
		IFeatureAttribute stringAttributeNull = attributeFactory.createStringAttribute(root, "sNull", "", null, true, true);
		IFeatureAttribute booleanAttributeNull = attributeFactory.createBooleanAttribute(root, "bNull", "", null, false, true);
		IFeatureAttribute longAttributeNull = attributeFactory.createLongAttribute(root, "lNull", "", null, true, false);
		IFeatureAttribute doubleAttributeNull = attributeFactory.createDoubleAttribute(root, "dNull", "", null, false, false);

		assertTrue(stringAttribute.getName().equals("stringTest"));
		assertTrue(stringAttribute.getUnit().equals("EMPTY"));
		assertTrue(stringAttribute.getValue().equals("Ein Test"));
		assertTrue(!stringAttribute.isRecursive());
		assertTrue(!stringAttribute.isConfigurable());

		assertTrue(booleanAttribute.getName().equals("booleanTest"));
		assertTrue(booleanAttribute.getUnit().equals("State"));
		assertTrue(booleanAttribute.getValue() == Boolean.TRUE);
		assertTrue(booleanAttribute.isRecursive());
		assertTrue(!booleanAttribute.isConfigurable());

		assertTrue(longAttribute.getName().equals("longTest"));
		assertTrue(longAttribute.getUnit().equals("Euro"));
		assertTrue(longAttribute.getValue().equals(Long.MAX_VALUE));
		assertTrue(!longAttribute.isRecursive());
		assertTrue(longAttribute.isConfigurable());

		assertTrue(doubleAttribute.getName().equals("doubleTest"));
		assertTrue(doubleAttribute.getUnit().equals("Dollar"));
		assertTrue(doubleAttribute.getValue().equals(Double.MAX_VALUE));
		assertTrue(doubleAttribute.isRecursive());
		assertTrue(doubleAttribute.isConfigurable());

		assertTrue(stringAttributeNull.getName().equals("sNull"));
		assertTrue(stringAttributeNull.getValue() == null);
		assertTrue(stringAttributeNull.getUnit().equals(""));
		assertTrue(stringAttributeNull.isRecursive());
		assertTrue(stringAttributeNull.isConfigurable());

		assertTrue(booleanAttributeNull.getName().equals("bNull"));
		assertTrue(booleanAttributeNull.getValue() == null);
		assertTrue(booleanAttributeNull.getUnit().equals(""));
		assertTrue(!booleanAttributeNull.isRecursive());
		assertTrue(booleanAttributeNull.isConfigurable());

		assertTrue(longAttributeNull.getName().equals("lNull"));
		assertTrue(longAttributeNull.getValue() == null);
		assertTrue(longAttributeNull.getUnit().equals(""));
		assertTrue(longAttributeNull.isRecursive());
		assertTrue(!longAttributeNull.isConfigurable());

		assertTrue(doubleAttributeNull.getName().equals("dNull"));
		assertTrue(doubleAttributeNull.getValue() == null);
		assertTrue(doubleAttributeNull.getUnit().equals(""));
		assertTrue(!doubleAttributeNull.isRecursive());
		assertTrue(!doubleAttributeNull.isConfigurable());
	}
}
