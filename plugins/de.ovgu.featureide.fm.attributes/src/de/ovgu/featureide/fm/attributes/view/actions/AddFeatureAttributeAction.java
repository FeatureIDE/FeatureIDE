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
package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;

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

/**
 * Action used to create an attribute. Depending on the {@link #attributeType} the action creates an attribute of the given type.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class AddFeatureAttributeAction extends Action {

	private final FeatureModelManager fmManager;
	private final String featureName;
	private final String attributeType;

	public AddFeatureAttributeAction(FeatureModelManager fmManager, String featureName, String attributeType, String actionName) {
		super(actionName);
		this.fmManager = fmManager;
		this.featureName = featureName;
		this.attributeType = attributeType;
	}

	@Override
	public void run() {
		fmManager.editObject(this::addAttribute, FeatureModelManager.CHANGE_ATTRIBUTES);
	}

	private void addAttribute(IFeatureModel featureModel) {
		final IExtendedFeature feature = (IExtendedFeature) featureModel.getFeature(featureName);
		final String name = getUniqueAttributeName(attributeType, feature);
		final IFeatureAttribute attribute;
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
			return;
		}
		feature.addAttribute(attribute);
		featureModel.fireEvent(new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, feature));
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
}
