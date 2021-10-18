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
package de.ovgu.featureide.fm.attributes.view.operations;

import de.ovgu.featureide.fm.attributes.AttributeUtils;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.BooleanFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;

/**
 * Operation to create an attribute. Enables undo/redo functionality.
 * 
 * @author Johannes Herschel
 */
public class AddFeatureAttributeOperation extends AbstractFeatureModelOperation {

	/**
	 * The name of the feature to contain the new attribute.
	 */
	private final String featureName;
	/**
	 * The type of the new attribute.
	 */
	private final String attributeType;

	/**
	 * The name of the created attribute.
	 */
	private String attributeName;

	public AddFeatureAttributeOperation(IFeatureModelManager featureModelManager, String featureName, String attributeType, String title) {
		super(featureModelManager, title);
		this.featureName = featureName;
		this.attributeType = attributeType;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		if (feature instanceof IExtendedFeature) {
			final IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			if (attributeName == null) {
				attributeName = getUniqueAttributeName(attributeType, extendedFeature);
			}
			IFeatureAttribute attribute;
			switch (attributeType) {
			case FeatureAttribute.BOOLEAN:
				attribute = new BooleanFeatureAttribute(extendedFeature, attributeName, "", null, false, false);
				break;
			case FeatureAttribute.DOUBLE:
				attribute = new DoubleFeatureAttribute(extendedFeature, attributeName, "", null, false, false);
				break;
			case FeatureAttribute.LONG:
				attribute = new LongFeatureAttribute(extendedFeature, attributeName, "", null, false, false);
				break;
			case FeatureAttribute.STRING:
				attribute = new StringFeatureAttribute(extendedFeature, attributeName, "", null, false, false);
				break;
			default:
				return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
			}
			extendedFeature.addAttribute(attribute);
			return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, extendedFeature);
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	/**
	 * Creates a unique name for an attribute of the given type contained in the given feature.
	 * 
	 * @param type The type of the attribute
	 * @param feature The containing feature of the attribute
	 * @return A unique name for an attribute of the given type contained in the given feature
	 */
	private String getUniqueAttributeName(String type, IExtendedFeature feature) {
		final String capitalizedType = type.substring(0, 1).toUpperCase() + type.substring(1);
		final String attributePrefix = capitalizedType + "Attribute";
		for (int i = 0;; i++) {
			final String attributeName = attributePrefix + i;
			if (feature.getAttribute(attributeName) == null) {
				return attributeName;
			}
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeatureAttribute attribute = AttributeUtils.getAttribute(featureModel, featureName, attributeName);
		if (attribute != null) {
			final IExtendedFeature extendedFeature = (IExtendedFeature) attribute.getFeature();
			extendedFeature.removeAttribute(attribute);
			return new FeatureIDEEvent(null, EventType.FEATURE_ATTRIBUTE_CHANGED, true, extendedFeature);
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ATTRIBUTES;
	}
}
