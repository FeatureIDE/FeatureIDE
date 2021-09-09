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

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.BooleanFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.StringFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;

/**
 * Operation to create an attribute.
 * 
 * @author Johannes Herschel
 */
public class AddFeatureAttributeOperation extends AbstractFeatureModelOperation {

	private final String featureName;
	private final String attributeType;

	private IFeatureAttribute attribute;

	public AddFeatureAttributeOperation(IFeatureModelManager featureModelManager, String featureName, String attributeType, String title) {
		super(featureModelManager, title);
		this.featureName = featureName;
		this.attributeType = attributeType;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		return featureModelManager.processObject(this::addAttribute, FeatureModelManager.CHANGE_ATTRIBUTES);
	}

	private FeatureIDEEvent addAttribute(IFeatureModel featureModel) {
		final IExtendedFeature feature = (IExtendedFeature) featureModel.getFeature(featureName);
		final String name = getUniqueAttributeName(attributeType, feature);
		switch (attributeType) {
		case FeatureAttribute.BOOLEAN:
			attribute = new BooleanFeatureAttribute(feature, name, "", null, false, false);
			break;
		case FeatureAttribute.DOUBLE:
			attribute = new DoubleFeatureAttribute(feature, name, "", null, false, false);
			break;
		case FeatureAttribute.LONG:
			attribute = new LongFeatureAttribute(feature, name, "", null, false, false);
			break;
		case FeatureAttribute.STRING:
			attribute = new StringFeatureAttribute(feature, name, "", null, false, false);
			break;
		default:
			return null;
		}
		feature.addAttribute(attribute);
		return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, feature);
	}

	private String getUniqueAttributeName(String type, IExtendedFeature feature) {
		int amountOfAttributes = 0;
		while (true) {
			boolean isUnique = true;
			String capitalizedType = type.substring(0, 1).toUpperCase() + type.substring(1);
			String attributeName = capitalizedType + "Attribute" + amountOfAttributes++;
			for (IFeatureAttribute att : feature.getAttributes()) {
				if (att.getName().equals(attributeName)) {
					isUnique = false;
					break;
				}
			}
			if (isUnique) {
				return attributeName;
			}
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		return featureModelManager.processObject(this::removeAttribute, FeatureModelManager.CHANGE_ATTRIBUTES);
	}

	private FeatureIDEEvent removeAttribute(IFeatureModel featureModel) {
		final IExtendedFeature feature = (IExtendedFeature) featureModel.getFeature(featureName);
		feature.removeAttribute(attribute);
		return new FeatureIDEEvent(null, EventType.FEATURE_ATTRIBUTE_CHANGED, true, feature);
	}
}
