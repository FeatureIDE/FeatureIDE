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

import java.util.HashMap;
import java.util.Map;

import org.junit.Test;

import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelObfuscator;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.ui.handlers.ObfuscatorHandler;

/**
 * TODO description
 * 
 * @author Rahel Arens
 * @author Benedikt Jutz
 */
public class ObfuscationExtendedFeatureModelsTest {

	@Test
	public void testSandwichModel() {
		// Load the Sandwich model with feature strings, and obfuscate it.
		String modelPathString = "SandwichModelWithStringAttributes.xml";
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
				// featName.attrName -> [featName, attrName]
				String[] attrNameParts = obfuscatedStrings.get(attribute.getKey()).split("/");
				String attrName = attrNameParts[1];
				// Deobfuscate String values: featName.attrName.attrValue -> [featName, attrName, attrValue]
				Object attrValue = attribute.getValue();
				if (attrValue instanceof String) {
					String[] attrValueParts = obfuscatedStrings.get(attrValue).split("/");
					if (attrValueParts.length == 3) {
						attrValue = attrValueParts[2];
					} else {
						attrValue = "";
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
	}
}
