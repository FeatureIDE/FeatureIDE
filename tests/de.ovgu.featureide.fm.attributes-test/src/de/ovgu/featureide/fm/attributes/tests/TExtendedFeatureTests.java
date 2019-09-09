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
import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;

/**
 * Tests used to verify the correct behavior for the {@link ExtendedFeature}
 * 
 * @author Joshua Sprey
 */
public class TExtendedFeatureTests {

	private static final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();
	private static final ExtendedFeatureModelFactory factory = new ExtendedFeatureModelFactory();

	@Before
	public void prepareWorkbench() {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
	}

	/**
	 * Checks {@link ExtendedFeature#getAttributes()}
	 */
	@Test
	public void test_getAttributes() {
		// Load model from file
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		ExtendedFeature breadFeature = (ExtendedFeature) model.getFeature("Bread");
		assertTrue(breadFeature.getAttributes() != null);
		assertTrue(breadFeature.getAttributes().size() == 3);

		ExtendedFeature hamFeature = (ExtendedFeature) model.getFeature("Ham");
		assertTrue(hamFeature.getAttributes() != null);
		assertTrue(hamFeature.getAttributes().size() == 3);

		ExtendedFeature lettuceFeature = (ExtendedFeature) model.getFeature("Lettuce");
		assertTrue(lettuceFeature.getAttributes() != null);
		assertTrue(lettuceFeature.getAttributes().size() == 3);
	}

	/**
	 * Checks {@link ExtendedFeature#addAttribute(IFeatureAttribute)}
	 */
	@Test
	public void test_addAttributes() {
		// Load model from file
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		// Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature) model.getFeature("Bread");
		// Create an attribute
		IFeatureAttribute attribute = attributeFactory.createStringAttribute(breadFeature, "test", "Test", "Test Value", false, false);
		// Add the attribute to the feature
		assertTrue(breadFeature.getAttributes().size() == 3);
		breadFeature.addAttribute(attribute);
		assertTrue(breadFeature.getAttributes().size() == 4);
		assertTrue(breadFeature.getAttributes().contains(attribute));
	}

	/**
	 * Checks {@link ExtendedFeature#removeAttribute(IFeatureAttribute)}
	 */
	@Test
	public void test_removeAttributes() {
		// Load model from file
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		// Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature) model.getFeature("Bread");
		// Create an attribute
		IFeatureAttribute attribute = attributeFactory.createStringAttribute(breadFeature, "test", "Test", "Test Value", false, false);
		// Add the attribute to the feature
		assertTrue(breadFeature.getAttributes().size() == 3);
		breadFeature.addAttribute(attribute);
		assertTrue(breadFeature.getAttributes().size() == 4);
		assertTrue(breadFeature.getAttributes().contains(attribute));
		breadFeature.removeAttribute(attribute);
		assertTrue(breadFeature.getAttributes().size() == 3);
		assertTrue(!breadFeature.getAttributes().contains(attribute));
	}

	/**
	 * Checks {@link ExtendedFeature#clone(IFeatureModel, de.ovgu.featureide.fm.core.base.IFeatureStructure)}
	 */
	@Test
	public void test_clone() {
		IFeatureModel model = factory.create();
		// Get a feature
		ExtendedFeature testFeature = factory.createFeature(model, "Test");

		// Create an attribute
		IFeatureAttribute attribute = attributeFactory.createStringAttribute(testFeature, "test", "Test", "Test Value", true, true);
		// Add the attribute to the feature
		testFeature.addAttribute(attribute);

		IFeature cloneF = testFeature.clone(testFeature.getFeatureModel(), testFeature.getStructure());

		assertTrue(cloneF instanceof ExtendedFeature);
		ExtendedFeature cloneExF = (ExtendedFeature) cloneF;
		assertTrue(cloneExF.getAttributes().size() == 1);
		IFeatureAttribute attributeClone = cloneExF.getAttributes().get(0);
		assertTrue(attributeClone.getFeature() == cloneExF);
		assertTrue(attributeClone.getName().equals("test"));
		assertTrue(attributeClone instanceof StringFeatureAttribute);
		assertTrue(attributeClone.getType().equals(FeatureAttribute.STRING));
		assertTrue(attributeClone.getUnit().equals("Test"));
		assertTrue(attributeClone.getValue().equals("Test Value"));
		assertTrue(attributeClone.isRecursive());
		assertTrue(attributeClone.isConfigurable());
	}

	/**
	 * Checks {@link ExtendedFeature#isContainingAttribute(IFeatureAttribute)}
	 */
	@Test
	public void test_isContainingAttribute() {
		// Load model from file
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		// Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature) model.getFeature("Bread");

		for (IFeatureAttribute att : breadFeature.getAttributes()) {
			assertTrue(breadFeature.isContainingAttribute(att));
		}
	}

	/**
	 * Checks {@link ExtendedFeature#createTooltip(Object...)}
	 */
	@Test
	public void test_createTooltip() {
		// Load model from file
		ExtendedFeatureModel model = Commons.getSandwitchModel();
		// Get a feature
		ExtendedFeature breadFeature = (ExtendedFeature) model.getFeature("Bread");
		// Create the tooltip
		String tooltip = breadFeature.createTooltip("");
		assertTrue(tooltip.contains("Inherited Attributes:"));
		assertTrue(tooltip.contains("recursive configureable long Calories = null"));
		assertTrue(tooltip.contains("recursive boolean Organic Food = null"));
		assertTrue(tooltip.contains("recursive double Price = null"));
	}
}
