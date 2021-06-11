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
package de.ovgu.featureide.fm.attributes.base.impl;

import java.security.MessageDigest;
import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.editing.FeatureModelObfuscator;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * ExtendedFeatureModelObfuscator obfuscates an {@link ExtendedFeatureModel} along with the names and string values of its feature attributes.
 * 
 * @see {@link FeatureModelObfuscator}
 * 
 * @author Rahel Arens
 * @author Benedikt Jutz
 */
public class ExtendedFeatureModelObfuscator extends FeatureModelObfuscator {

	private final IFeatureModel orgFeatureModel;
	private IFeatureModel obfuscatedFeatureModel;
	private Map<String, String> obfuscatedStrings;

	public Map<String, String> getObfuscatedStrings() {
		return obfuscatedStrings;
	}

	public ExtendedFeatureModelObfuscator(IFeatureModel featureModel) {
		super(featureModel);

		orgFeatureModel = featureModel;
		obfuscatedStrings = new HashMap<>();
	}

	public ExtendedFeatureModelObfuscator(IFeatureModel featureModel, String salt) {
		super(featureModel, salt);

		orgFeatureModel = featureModel;
		obfuscatedStrings = new HashMap<>();
	}

	@Override
	public IFeatureModel execute(IMonitor<IFeatureModel> monitor) throws Exception {

		if (!(orgFeatureModel instanceof ExtendedFeatureModel)) {
			return super.execute(monitor);
		}

		digest = MessageDigest.getInstance("SHA-256");
		obfuscatedFeatureModel = factory.create();
		obfuscateStructure(orgFeatureModel.getStructure().getRoot(), null);
		super.obfuscateConstraints();
		return obfuscatedFeatureModel;
	}

	private void obfuscateStructure(IFeatureStructure orgFeatureStructure, IFeature parentFeature) {
		final ExtendedFeature orgFeature = (ExtendedFeature) orgFeatureStructure.getFeature();

		final String obfuscatedFeatureName = getObfuscatedFeatureName(orgFeature.getName());
		obfuscatedStrings.put(obfuscatedFeatureName, orgFeature.getName());
		final ExtendedFeature obfuscatedFeature = (ExtendedFeature) factory.createFeature(obfuscatedFeatureModel, obfuscatedFeatureName);
		final String description = orgFeatureStructure.getFeature().getProperty().getDescription();
		if ((description != null) && !description.isEmpty()) {
			obfuscatedFeature.getProperty().setDescription(getObfuscatedDescription(description));
		}

		final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();

		for (IFeatureAttribute attribute : orgFeature.getAttributes()) {

			IFeatureAttribute obfFeatureAttribute = null;

			final String obfAttributeName = getObfuscatedFeatureAttributeName(attribute.getName());
			obfuscatedStrings.put(obfAttributeName, orgFeature.getName() + "/" + attribute.getName());

			switch (attribute.getType()) {
			case FeatureAttribute.BOOLEAN:
				obfFeatureAttribute = attributeFactory.createBooleanAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(),
						(Boolean) attribute.getValue(), attribute.isRecursive(), attribute.isConfigurable());
				break;
			case FeatureAttribute.DOUBLE:
				obfFeatureAttribute = attributeFactory.createDoubleAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(),
						(Double) attribute.getValue(), attribute.isRecursive(), attribute.isConfigurable());
				break;
			case FeatureAttribute.LONG:
				obfFeatureAttribute = attributeFactory.createLongAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(),
						(Long) attribute.getValue(), attribute.isRecursive(), attribute.isConfigurable());
				break;
			case FeatureAttribute.STRING:
				String oldValue = (String) attribute.getValue();
				if (oldValue == null) {
					oldValue = "";
				}
				String obfuscatedValue = getObfuscatedStringValue(oldValue);
				obfuscatedStrings.put(obfuscatedValue, orgFeature.getName() + "/" + attribute.getName() + "/" + oldValue);
				obfFeatureAttribute = attributeFactory.createStringAttribute(obfuscatedFeature, obfAttributeName, attribute.getUnit(), obfuscatedValue,
						attribute.isRecursive(), attribute.isConfigurable());
			}
			obfuscatedFeature.addAttribute(obfFeatureAttribute);
		}

		obfuscatedFeatureModel.addFeature(obfuscatedFeature);
		final IFeatureStructure obfuscatedFeatureStructure = obfuscatedFeature.getStructure();
		obfuscatedFeatureStructure.setAbstract(orgFeatureStructure.isAbstract());
		obfuscatedFeatureStructure.setMandatory(orgFeatureStructure.isMandatory());
		obfuscatedFeatureStructure.setAND(orgFeatureStructure.isAnd());
		obfuscatedFeatureStructure.setMultiple(orgFeatureStructure.isMultiple());
		obfuscatedFeatureStructure.setHidden(orgFeatureStructure.isHidden());
		if (parentFeature == null) {
			obfuscatedFeatureModel.getStructure().setRoot(obfuscatedFeatureStructure);
		} else {
			parentFeature.getStructure().addChild(obfuscatedFeatureStructure);
		}

		for (final IFeatureStructure orgChildStructure : orgFeatureStructure.getChildren()) {
			obfuscateStructure(orgChildStructure, obfuscatedFeature);
		}
	}

	private String getObfuscatedStringValue(String orgValue) {
		return obfuscate(orgValue, new char[RESULT_LENGTH]);
	}

	private String getObfuscatedFeatureAttributeName(String attributeName) {
		return obfuscate(attributeName, new char[RESULT_LENGTH]);
	}

}
