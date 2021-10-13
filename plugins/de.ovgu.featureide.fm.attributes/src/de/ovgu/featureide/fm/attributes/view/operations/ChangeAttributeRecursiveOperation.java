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

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_ATTRIBUTE_RECURSIVE_OPERATION_NAME;

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
 * Operation to change whether a feature attribute is recursive.
 * 
 * @author Johannes Herschel
 */
public class ChangeAttributeRecursiveOperation extends AbstractFeatureModelOperation {

	/**
	 * The name of the feature containing the attribute to be modified.
	 */
	private final String featureName;
	/**
	 * The name of the attribute to be modified.
	 */
	private final String attributeName;
	/**
	 * Whether the attribute is recursive after the operation.
	 */
	private final boolean newRecursive;

	/**
	 * Whether the attribute is recursive before the operation.
	 */
	private final boolean oldRecursive;

	public ChangeAttributeRecursiveOperation(IFeatureModelManager featureModelManager, IFeatureAttribute attribute, boolean newRecursive) {
		super(featureModelManager, CHANGE_ATTRIBUTE_RECURSIVE_OPERATION_NAME);
		featureName = attribute.getFeature().getName();
		attributeName = attribute.getName();
		this.newRecursive = newRecursive;

		oldRecursive = attribute.isRecursive();
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		if (newRecursive == oldRecursive) {
			return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
		}

		IFeature feature = featureModel.getFeature(featureName);
		if (feature instanceof IExtendedFeature) {
			IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			IFeatureAttribute attribute = extendedFeature.getAttribute(attributeName);
			if (attribute != null) {
				attribute.setRecursive(newRecursive);
				if (newRecursive) {
					attribute.addRecursiveAttributes();
				} else {
					attribute.deleteRecursiveAttributes();
				}
				return new FeatureIDEEvent(attribute, EventType.FEATURE_ATTRIBUTE_CHANGED, true, extendedFeature);
			}
		}
		return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (newRecursive == oldRecursive) {
			return FeatureIDEEvent.getDefault(EventType.FEATURE_ATTRIBUTE_CHANGED);
		}

		IFeature feature = featureModel.getFeature(featureName);
		if (feature instanceof IExtendedFeature) {
			IExtendedFeature extendedFeature = (IExtendedFeature) feature;
			IFeatureAttribute attribute = extendedFeature.getAttribute(attributeName);
			if (attribute != null) {
				attribute.setRecursive(oldRecursive);
				if (oldRecursive) {
					attribute.addRecursiveAttributes();
				} else {
					attribute.deleteRecursiveAttributes();
				}
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
