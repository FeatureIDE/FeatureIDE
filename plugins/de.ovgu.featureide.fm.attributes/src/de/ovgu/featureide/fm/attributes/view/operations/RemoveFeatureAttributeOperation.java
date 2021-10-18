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

import static de.ovgu.featureide.fm.core.localization.StringTable.REMOVE_ATTRIBUTE_OPERATION_NAME;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.ovgu.featureide.fm.attributes.AttributeUtils;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;

/**
 * Operation to remove feature attributes. Enables undo/redo functionality.
 * 
 * @author Johannes Herschel
 */
public class RemoveFeatureAttributeOperation extends AbstractFeatureModelOperation {

	/**
	 * Pair of feature name and attribute name.
	 * 
	 * @author Johannes Herschel
	 */
	private static class FeatureAttributeDescriptor {

		public final String featureName;
		public final String attributeName;

		public FeatureAttributeDescriptor(String featureName, String attributeName) {
			this.featureName = featureName;
			this.attributeName = attributeName;
		}
	}

	/**
	 * Attributes to be removed.
	 */
	private final List<FeatureAttributeDescriptor> attributes;

	/**
	 * Map of removed attributes and the names of their features.
	 */
	private final Map<IFeatureAttribute, String> removedAttributes;

	public RemoveFeatureAttributeOperation(IFeatureModelManager featureModelManager, List<IFeatureAttribute> attributes) {
		super(featureModelManager, REMOVE_ATTRIBUTE_OPERATION_NAME);

		this.attributes = new ArrayList<>(attributes.size());
		for (IFeatureAttribute a : attributes) {
			this.attributes.add(new FeatureAttributeDescriptor(a.getFeature().getName(), a.getName()));
		}

		removedAttributes = new HashMap<>(attributes.size());
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		removedAttributes.clear();
		for (final FeatureAttributeDescriptor attributeDescriptor : attributes) {
			final IFeatureAttribute attribute = AttributeUtils.getAttribute(featureModel, attributeDescriptor.featureName, attributeDescriptor.attributeName);
			if (attribute != null) {
				final IExtendedFeature extendedFeature = (IExtendedFeature) attribute.getFeature();
				if (attribute.isRecursive()) {
					if (attribute.isHeadOfRecursiveAttribute()) {
						attribute.deleteRecursiveAttributes(); // Saves values of descendants in the attribute
						removedAttributes.put(attribute, attributeDescriptor.featureName);
						extendedFeature.removeAttribute(attribute);
					}
				} else {
					removedAttributes.put(attribute, attributeDescriptor.featureName);
					extendedFeature.removeAttribute(attribute);
				}
			}
		}
		return new FeatureIDEEvent(null, EventType.FEATURE_ATTRIBUTE_CHANGED, true, FeatureUtils.getRoot(featureModel));
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		for (final Map.Entry<IFeatureAttribute, String> removedAttribute : removedAttributes.entrySet()) {
			final IFeature feature = featureModel.getFeature(removedAttribute.getValue());
			if (feature instanceof IExtendedFeature) {
				final IExtendedFeature extendedFeature = (IExtendedFeature) feature;
				final IFeatureAttribute attribute = removedAttribute.getKey().cloneAtt(extendedFeature);
				extendedFeature.addAttribute(attribute);
				if (attribute.isRecursive()) {
					attribute.addRecursiveAttributes(); // Restores values of descendants
				}
			}
		}
		return new FeatureIDEEvent(null, EventType.FEATURE_ATTRIBUTE_CHANGED, true, FeatureUtils.getRoot(featureModel));
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ATTRIBUTES;
	}
}
