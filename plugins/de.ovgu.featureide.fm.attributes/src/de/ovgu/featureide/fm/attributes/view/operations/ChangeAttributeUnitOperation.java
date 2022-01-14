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

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_ATTRIBUTE_UNIT_OPERATION_NAME;

import de.ovgu.featureide.fm.attributes.AttributeUtils;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;

/**
 * Operation to change the unit of a feature attribute. Enables undo/redo functionality.
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
	/**
	 * The new unit of the attribute after the operation.
	 */
	private final String newUnit;

	/**
	 * The old unit of the attribute before the operation.
	 */
	private final String oldUnit;

	public ChangeAttributeUnitOperation(IFeatureModelManager featureModelManager, IFeatureAttribute attribute, String newUnit) {
		super(featureModelManager, CHANGE_ATTRIBUTE_UNIT_OPERATION_NAME);
		featureName = attribute.getFeature().getName();
		attributeName = attribute.getName();
		this.newUnit = newUnit;

		oldUnit = attribute.getUnit();
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeatureAttribute attribute = AttributeUtils.getAttribute(featureModel, featureName, attributeName);
		if (attribute != null) {
			attribute.setUnit(newUnit);
			return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, attribute.getFeature());
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeatureAttribute attribute = AttributeUtils.getAttribute(featureModel, featureName, attributeName);
		if (attribute != null) {
			attribute.setUnit(oldUnit);
			return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, attribute.getFeature());
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ATTRIBUTES;
	}
}
