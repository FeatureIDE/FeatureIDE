// /* FeatureIDE - A Framework for Feature-Oriented Software Development
//  * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
//  *
//  * This file is part of FeatureIDE.
//  * 
//  * FeatureIDE is free software: you can redistribute it and/or modify
//  * it under the terms of the GNU Lesser General Public License as published by
//  * the Free Software Foundation, either version 3 of the License, or
//  * (at your option) any later version.
//  * 
//  * FeatureIDE is distributed in the hope that it will be useful,
//  * but WITHOUT ANY WARRANTY; without even the implied warranty of
//  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  * GNU Lesser General Public License for more details.
//  * 
//  * You should have received a copy of the GNU Lesser General Public License
//  * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
//  *
//  * See http://featureide.cs.ovgu.de/ for further information.
//  */
// package de.ovgu.featureide.fm.attributes.tests;

// import static org.junit.Assert.assertEquals;
// import static org.junit.Assert.assertFalse;
// import static org.junit.Assert.assertTrue;

// import java.util.List;
// import java.util.stream.Collectors;

// import org.junit.Before;
// import org.junit.Test;

// import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
// import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
// import de.ovgu.featureide.fm.attributes.base.impl.BooleanFeatureAttribute;
// import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
// import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeature;
// import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModel;
// import de.ovgu.featureide.fm.attributes.base.impl.ExtendedMultiFeatureModelFactory;
// import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
// import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
// import de.ovgu.featureide.fm.attributes.format.UVLExtendedFeatureModelFormat;
// import de.ovgu.featureide.fm.core.base.IFeatureStructure;
// import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
// import de.ovgu.featureide.fm.core.init.LibraryManager;
// import de.ovgu.featureide.fm.core.io.uvl.UVLFeatureModelFormat;

// /**
//  * Tests for writing and reading extended UVL models
//  * 
//  * @author Rahel Arens
//  * @author Johannes Herschel
//  */
// public class TExtendedMultiFeatureModelSaveAndLoad {

// 	private static final ExtendedMultiFeatureModelFactory factory = new ExtendedMultiFeatureModelFactory();

// 	@Before
// 	public void prepareWorkbench() {
// 		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
// 		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
// 	}

// 	@Test
// 	public void testCreateWriteRead() {
// 		// Create model
// 		ExtendedMultiFeatureModel model = factory.create();
// 		ExtendedMultiFeature rootFeature = factory.createFeature(model, "Root");
// 		rootFeature.getStructure().setAbstract(true);
// 		model.addFeature(rootFeature);
// 		model.getStructure().setRoot(rootFeature.getStructure());
// 		ExtendedMultiFeature baseFeature = factory.createFeature(model, "Base");
// 		model.addFeature(baseFeature);
// 		rootFeature.getStructure().addChild(baseFeature.getStructure());

// 		// Test structure
// 		assertEquals(2, model.getNumberOfFeatures());
// 		assertEquals("Root", rootFeature.getName());
// 		assertEquals(1, rootFeature.getStructure().getChildrenCount());
// 		assertTrue(rootFeature.getStructure().isAnd());
// 		assertTrue(!rootFeature.getStructure().isOr());
// 		assertTrue(!rootFeature.getStructure().isAlternative());
// 		assertEquals("Base", rootFeature.getStructure().getChildren().get(0).getFeature().getName());

// 		// No attributes when created by factory
// 		assertEquals(0, rootFeature.getAttributes().size());
// 		assertEquals(0, baseFeature.getAttributes().size());

// 		// Create and add attributes
// 		IFeatureAttribute stringAttribute = new StringFeatureAttribute(rootFeature, "stringAttr", "stringUnit", "stringVal", false, false);
// 		IFeatureAttribute booleanAttribute = new BooleanFeatureAttribute(rootFeature, "boolAttr", "boolUnit", false, true, false);
// 		IFeatureAttribute longAttribute = new LongFeatureAttribute(rootFeature, "longAttr", "longUnit", 42L, false, true);
// 		IFeatureAttribute doubleAttribute = new DoubleFeatureAttribute(rootFeature, "doubleAttr", "doubleUnit", 17.25, true, true);

// 		rootFeature.addAttribute(stringAttribute);
// 		rootFeature.addAttribute(booleanAttribute);
// 		rootFeature.addAttribute(longAttribute);
// 		rootFeature.addAttribute(doubleAttribute);

// 		IFeatureAttribute stringAttributeNull = new StringFeatureAttribute(baseFeature, "stringAttrNull", "stringUnitNull", null, true, true);
// 		IFeatureAttribute booleanAttributeNull = new BooleanFeatureAttribute(baseFeature, "boolAttrNull", "boolUnitNull", null, false, true);
// 		IFeatureAttribute longAttributeNull = new LongFeatureAttribute(baseFeature, "longAttrNull", "longUnitNull", null, true, false);
// 		IFeatureAttribute doubleAttributeNull = new DoubleFeatureAttribute(baseFeature, "doubleAttrNull", null, null, false, false);

// 		baseFeature.addAttribute(stringAttributeNull);
// 		baseFeature.addAttribute(booleanAttributeNull);
// 		baseFeature.addAttribute(longAttributeNull);
// 		baseFeature.addAttribute(doubleAttributeNull);

// 		// Test attributes
// 		assertEquals(4, rootFeature.getAttributes().size());
// 		assertEquals(4, baseFeature.getAttributes().size());

// 		// Write and read model
// 		UVLExtendedFeatureModelFormat extendedFormat = new UVLExtendedFeatureModelFormat();
// 		UVLFeatureModelFormat format = new UVLFeatureModelFormat();
// 		String uvlSource = extendedFormat.getInstance().write(model);
// 		assertTrue(extendedFormat.supportsContent(uvlSource));
// 		assertFalse(format.supportsContent(uvlSource));

// 		ExtendedMultiFeatureModel newModel = factory.create();
// 		extendedFormat.getInstance().read(newModel, uvlSource);

// 		// Compare structure of new model to original structure
// 		assertEquals(2, newModel.getNumberOfFeatures());
// 		IFeatureStructure newRootStructure = newModel.getStructure().getRoot();
// 		assertTrue(newRootStructure.getFeature() instanceof ExtendedMultiFeature);
// 		assertEquals("Root", newRootStructure.getFeature().getName());
// 		assertTrue(newRootStructure.isRoot());
// 		assertTrue(newRootStructure.isAbstract());
// 		assertEquals(1, newRootStructure.getChildrenCount());
// 		IFeatureStructure newBaseStructure = newRootStructure.getChildren().get(0);
// 		assertTrue(newBaseStructure.getFeature() instanceof ExtendedMultiFeature);
// 		assertEquals("Base", newBaseStructure.getFeature().getName());
// 		assertFalse(newBaseStructure.isRoot());
// 		assertFalse(newBaseStructure.isAbstract());
// 		assertEquals(0, newBaseStructure.getChildrenCount());

// 		// Compare attributes
// 		compareAttributes(rootFeature, (ExtendedMultiFeature) newRootStructure.getFeature());
// 		compareAttributes(baseFeature, (ExtendedMultiFeature) newBaseStructure.getFeature());
// 	}

// 	private void compareAttributes(ExtendedMultiFeature expected, ExtendedMultiFeature actual) {
// 		List<IFeatureAttribute> expectedAttributes =
// 			expected.getAttributes().stream().sorted((a1, a2) -> a1.getName().compareTo(a2.getName())).collect(Collectors.toList());
// 		List<IFeatureAttribute> actualAttributes =
// 			actual.getAttributes().stream().sorted((a1, a2) -> a1.getName().compareTo(a2.getName())).collect(Collectors.toList());
// 		assertEquals(expectedAttributes.size(), actualAttributes.size());
// 		for (int i = 0; i < actualAttributes.size(); i++) {
// 			compareAttribute(expectedAttributes.get(i), actualAttributes.get(i));
// 		}
// 	}

// 	private void compareAttribute(IFeatureAttribute expected, IFeatureAttribute actual) {
// 		assertEquals(expected.getName(), actual.getName());
// 		assertEquals(expected.getType(), actual.getType());
// 		assertEquals(expected.getValue(), actual.getValue());
// 		assertEquals(expected.getUnit(), actual.getUnit());
// 		assertEquals(expected.isRecursive(), actual.isRecursive());
// 		assertEquals(expected.isConfigurable(), actual.isConfigurable());
// 	}
// }
