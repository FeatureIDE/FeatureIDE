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
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;

/**
 * Operation to edit the unit of a feature attribute.
 * 
 * @author Johannes Herschel
 */
public class ChangeAttributeUnitOperation extends AbstractFeatureModelOperation {

	/**
	 * The name of the feature containing the attribute to be modified.
	 */
	private final String featureName;
	/**
	 * The name of the attribute to be modified.
	 */
	private final String attributeName;
	private final String value;

	private final String oldValue;

	public ChangeAttributeUnitOperation(IFeatureModelManager featureModelManager, IFeatureAttribute attribute, String value) {
		super(featureModelManager, "Edit Attribute Unit");
		featureName = attribute.getFeature().getName();
		attributeName = attribute.getName();
		this.value = value;

		oldValue = attribute.getUnit();
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		IFeature feature = featureModel.getFeature(featureName);
		if (feature instanceof IExtendedFeature) {
			IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			IFeatureAttribute attribute = extendedFeature.getAttribute(attributeName);
			if (attribute != null) {
				attribute.setUnit(value);
				return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, extendedFeature);
			}
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		IFeature feature = featureModel.getFeature(featureName);
		if (feature instanceof IExtendedFeature) {
			IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			IFeatureAttribute attribute = extendedFeature.getAttribute(attributeName);
			if (attribute != null) {
				attribute.setUnit(oldValue);
				return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, extendedFeature);
			}
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ATTRIBUTES;
	}
}
