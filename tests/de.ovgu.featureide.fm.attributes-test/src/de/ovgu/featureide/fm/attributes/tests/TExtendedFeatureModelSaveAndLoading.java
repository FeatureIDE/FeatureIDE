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
package de.ovgu.featureide.fm.attributes.tests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;

/**
 * Test suit containing multiple tests to ensure the correct operation of
 * extended feature models.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class TExtendedFeatureModelSaveAndLoading {

	private static final IFeatureModelFactory factory = new ExtendedFeatureModelFactory();
	private static final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();

	@Test
	public void test_CreationAndSaving() {
		FMFactoryManager.getInstance().addExtension(new ExtendedFeatureModelFactory());
		FMFormatManager.getInstance().addExtension(new XmlExtendedFeatureModelFormat());

		// At first create an empty extended feature model
		IFeatureModel model = factory.create();
		IFeature rootFeature = factory.createFeature(model, "Root");
		model.addFeature(rootFeature);
		model.getStructure().setRoot(rootFeature.getStructure());
		IFeature baseFeature = factory.createFeature(model, "Base");
		model.addFeature(baseFeature);
		rootFeature.getStructure().addChild(baseFeature.getStructure());

		//Test structure and attributes of the features
		assertEquals(2, model.getNumberOfFeatures());
		assertEquals(rootFeature.getName(), "Root");
		assertEquals(rootFeature.getStructure().getChildrenCount(), 1);
		assertTrue(rootFeature.getStructure().isAnd());
		assertTrue(!rootFeature.getStructure().isOr());
		assertTrue(!rootFeature.getStructure().isAlternative());
		assertEquals(rootFeature.getStructure().getChildren().get(0).getFeature().getName(), "Base");
		assertTrue(model instanceof ExtendedFeatureModel);
		assertTrue(rootFeature instanceof ExtendedFeature);
		assertTrue(baseFeature instanceof ExtendedFeature);

		//Get the extended subclasses
		ExtendedFeatureModel eModel = (ExtendedFeatureModel) model;
		ExtendedFeature eRootFeature = (ExtendedFeature) rootFeature;
		ExtendedFeature eBaseFeature= (ExtendedFeature) baseFeature;
		
		//No attribute when created by factory
		assertTrue(eRootFeature.getAttributes().size() == 0);
		assertTrue(eBaseFeature.getAttributes().size() == 0);
		
		//Create all types of attributes with values
		IFeatureAttribute stringAttribute = attributeFactory.createStringAttribute(eRootFeature, "stringTest", "EMPTY", "Ein Test", false, false);
		IFeatureAttribute booleanAttribute = attributeFactory.createBooleanAttribute(eRootFeature, "booleanTest", "State", true, false, false);
		IFeatureAttribute longAttribute = attributeFactory.createLongAttribute(eRootFeature, "longTest", "Euro", Long.MAX_VALUE, false, false);
		IFeatureAttribute doubleAttribute = attributeFactory.createDoubleAttribute(eRootFeature, "doubleTest", "Dollar", Double.MAX_VALUE, false, false);

		//Create all types of attributes with null values
		IFeatureAttribute stringAttributeNull = attributeFactory.createStringAttribute(eRootFeature, "sNull", "", null, false, false);
		IFeatureAttribute booleanAttributeNull = attributeFactory.createBooleanAttribute(eRootFeature, "bNull", "", null, false, false);
		IFeatureAttribute longAttributeNull = attributeFactory.createLongAttribute(eRootFeature, "lNull", "", null, false, false);
		IFeatureAttribute doubleAttributeNull = attributeFactory.createDoubleAttribute(eRootFeature, "dNull", "", null, false, false);
		
		//Add the attributes to the feature 
		eRootFeature.addAttribute(stringAttribute);
		eRootFeature.addAttribute(booleanAttribute);
		eRootFeature.addAttribute(longAttribute);
		eRootFeature.addAttribute(doubleAttribute);
		eRootFeature.addAttribute(stringAttributeNull);
		eRootFeature.addAttribute(booleanAttributeNull);
		eRootFeature.addAttribute(longAttributeNull);
		eRootFeature.addAttribute(doubleAttributeNull);
		
		assertTrue(eRootFeature.getAttributes().size() == 8);
		
		//Save and load model
		IFeatureModel readModel = writeAndReadModel(eModel);
		
		//Compare the attributes
		assertTrue(readModel.getNumberOfFeatures() == 2);
		assertTrue(readModel instanceof ExtendedFeatureModel);
		assertTrue(readModel.getStructure().getRoot().getFeature() instanceof ExtendedFeature);
		assertTrue(readModel.getStructure().getRoot().getChildren().get(0).getFeature() instanceof ExtendedFeature);

		//Get the extended subclasses
		ExtendedFeature eReadRootFeature = (ExtendedFeature) readModel.getStructure().getRoot().getFeature();
		ExtendedFeature eReadBaseFeature= (ExtendedFeature) readModel.getStructure().getRoot().getChildren().get(0).getFeature();

		assertTrue(eReadRootFeature.getAttributes().size() == 8);
		assertTrue(eReadBaseFeature.getAttributes().size() == 0);

		stringAttribute = eReadRootFeature.getAttributes().get(0);
		booleanAttribute = eReadRootFeature.getAttributes().get(1);
		longAttribute = eReadRootFeature.getAttributes().get(2);
		doubleAttribute = eReadRootFeature.getAttributes().get(3);

		assertTrue(stringAttribute.getName().equals("stringTest"));
		assertTrue(stringAttribute.getUnit().equals("EMPTY"));
		assertTrue(stringAttribute.getValue().equals("Ein Test"));
		assertTrue(!stringAttribute.isRecursive());
		assertTrue(!stringAttribute.isConfigurable());

		assertTrue(booleanAttribute.getName().equals("booleanTest"));
		assertTrue(booleanAttribute.getUnit().equals("State"));
		assertTrue(booleanAttribute.getValue() == Boolean.TRUE);
		assertTrue(!booleanAttribute.isRecursive());
		assertTrue(!booleanAttribute.isConfigurable());

		assertTrue(longAttribute.getName().equals("longTest"));
		assertTrue(longAttribute.getUnit().equals("Euro"));
		assertTrue(longAttribute.getValue().equals(Long.MAX_VALUE));
		assertTrue(!longAttribute.isRecursive());
		assertTrue(!longAttribute.isConfigurable());

		assertTrue(doubleAttribute.getName().equals("doubleTest"));
		assertTrue(doubleAttribute.getUnit().equals("Dollar"));
		assertTrue(doubleAttribute.getValue().equals(Double.MAX_VALUE));
		assertTrue(!doubleAttribute.isRecursive());
		assertTrue(!doubleAttribute.isConfigurable());
		
		//Check Attributes with null values
		IFeatureAttribute sN = eReadRootFeature.getAttributes().get(4);
		IFeatureAttribute bN= eReadRootFeature.getAttributes().get(5);
		IFeatureAttribute lN= eReadRootFeature.getAttributes().get(6);
		IFeatureAttribute dN= eReadRootFeature.getAttributes().get(7);

		assertTrue(sN.getName().equals("sNull"));
		assertTrue(sN.getValue() == null);
		assertTrue(bN.getName().equals("bNull"));
		assertTrue(bN.getValue() == null);
		assertTrue(lN.getName().equals("lNull"));
		assertTrue(lN.getValue() == null);
		assertTrue(dN.getName().equals("dNull"));
		assertTrue(dN.getValue() == null);
	}

	
	private final IFeatureModel writeAndReadModel(IFeatureModel origFm) {
		IFeatureModel newFm = factory.create();
		final IFeatureModelFormat format = new XmlExtendedFeatureModelFormat();
		final String write = format.getInstance().write(origFm);
		format.getInstance().read(newFm, write);
		return newFm;
	}
}
