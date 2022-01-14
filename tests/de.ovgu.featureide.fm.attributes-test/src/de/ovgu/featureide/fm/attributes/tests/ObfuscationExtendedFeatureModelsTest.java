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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.fm.attributes.FMAttributesLibrary;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelObfuscator;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.ui.handlers.ObfuscatorHandler;

/**
 * Test that obfuscation of {@link ExtendedFeatureModel}s using {@link ExtendedFeatureModelObfuscator} works, i.e. feature names, their attribute names and
 * string attribute values are obfuscated (without changing the structure/other attribute properties).
 * 
 * @author Rahel Arens
 * @author Benedikt Jutz
 */
public class ObfuscationExtendedFeatureModelsTest {

	@Before
	public void prepareWorkbench() {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		LibraryManager.registerLibrary(FMAttributesLibrary.getInstance());
	}

	@Test
	public void testBasicModel() {
		testModelEquivalency("BaseExtendedFeatureModel.xml");
	}

	@Test
	public void testSandwichModel() {
		testModelEquivalency("SandwichModel.xml");
	}

	@Test
	public void testSandwichModelWithStrings() {
		testModelEquivalency("SandwichModelWithStringAttributes.xml");
	}

	/**
	 * Obfuscates the model under modelPathString, then deobfuscates its feature attributes and verifies the equivalency. Also verfies that the structural
	 * properties of the obfuscated and non-obfuscated model remain the same.
	 * 
	 * @param modelPathString - {@link String}
	 */
	public void testModelEquivalency(String modelPathString) {
		// Load the given model with feature strings, and obfuscate it.
		ExtendedFeatureModel model = (ExtendedFeatureModel) Commons.loadTestExtendedFeatureModelFromFile(modelPathString);
		String salt = new ObfuscatorHandler().getSalt(Commons.getRemoteOrLocalFolder(Commons.TEST_FEATURE_MODEL_PATH + modelPathString).toPath());
		ExtendedFeatureModelObfuscator obfuscator = new ExtendedFeatureModelObfuscator(model, salt);
		ExtendedFeatureModel obfuscatedModel = (ExtendedFeatureModel) LongRunningWrapper.runMethod(obfuscator);
		Map<String, String> obfuscatedStrings = obfuscator.getObfuscatedStrings();

		// Get the obfuscated attributes and create an deobfuscated equivalent.
		Map<String, Map<String, Object>> attributeMap = Commons.extractValueMap(obfuscatedModel);
		Map<String, Map<String, Object>> attributesDeobfuscated = new HashMap<>();

		for (Map.Entry<String, Map<String, Object>> entry : attributeMap.entrySet()) {
			// Get the feature name.
			String featName = obfuscatedStrings.get(entry.getKey());
			Map<String, Object> featAttrs = new HashMap<>();
			for (Map.Entry<String, Object> attribute : entry.getValue().entrySet()) {
				// featName/attrName -> [featName, attrName]
				String[] attrNameParts = obfuscatedStrings.get(featName + "/" + attribute.getKey()).split("/");
				String attrName = attrNameParts[1];

				// Deobfuscate String values: featName/attrName/attrValue -> [featName, attrName, attrValue]
				Object attrValue = attribute.getValue();
				if (attrValue instanceof String) {
					String[] attrValueParts = obfuscatedStrings.get(featName + "/" + attrName + "/" + attrValue).split("/");
					if (attrValueParts.length == 3) {
						attrValue = attrValueParts[2];
					} else {
						attrValue = null;
					}
				}
				// Add new attributes.
				featAttrs.put(attrName, attrValue);
			}
			// Add attributes for features.
			attributesDeobfuscated.put(featName, featAttrs);
		}
		// Verify the deobfuscated attributes.
		assertTrue(Commons.compareModelToValueMap(model, attributesDeobfuscated));

		// Assert that each obfuscated feature has the same structure/properties
		// (And|Or|Alternative Group, # of children, Mandatory|Optional, Abstract, Hidden)
		Map<String, IFeature> oldFeatures = model.getFeatureTable();
		for (IFeature feature : obfuscatedModel.getFeatures()) {
			ExtendedFeature obsFeature = (ExtendedFeature) feature;
			ExtendedFeature extFeature = (ExtendedFeature) oldFeatures.get(obfuscatedStrings.get(obsFeature.getName()));
			assertNotNull(extFeature);

			IFeatureStructure obsFeatureStruct = obsFeature.getStructure();
			IFeatureStructure extFeatureStructure = extFeature.getStructure();

			assertEquals(obsFeatureStruct.isAnd(), extFeatureStructure.isAnd());
			assertEquals(obsFeatureStruct.isAlternative(), extFeatureStructure.isAlternative());
			assertEquals(obsFeatureStruct.isOr(), extFeatureStructure.isOr());
			assertEquals(obsFeatureStruct.getChildrenCount(), extFeatureStructure.getChildrenCount());
			assertEquals(obsFeatureStruct.isMandatory(), extFeatureStructure.isMandatory());
			assertEquals(obsFeatureStruct.isAbstract(), extFeatureStructure.isAbstract());
			assertEquals(obsFeatureStruct.isHidden(), extFeatureStructure.isHidden());
		}

		// Assert that the obfuscated feature model contains the same constraints, except with obfuscated names.
		// Therefore assert that all feature names can be mapped to their deobfuscated equivalents.
		assertEquals(model.getConstraintCount(), obfuscatedModel.getConstraintCount());
		for (int iC = 0; iC < model.getConstraintCount(); iC++) {
			final IConstraint obfuscatedConstraint = obfuscatedModel.getConstraints().get(iC);
			final IConstraint constraint = model.getConstraints().get(iC);
			List<String> constraintFeatureNames = new ArrayList<>();
			for (IFeature feature : constraint.getContainedFeatures()) {
				constraintFeatureNames.add(feature.getName());
			}

			for (IFeature obsFeature : obfuscatedConstraint.getContainedFeatures()) {
				assertTrue(constraintFeatureNames.contains(obfuscatedStrings.get(obsFeature.getName())));
			}
		}
	}
}
