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

import java.util.List;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Action for the {@link FeatureAttributeView}. Is used to to remove the currently selected feature attribute.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class RemoveFeatureAttributeAction extends Action {

	private final IFeatureModelManager fmManager;
	private final List<IFeatureAttribute> attributes;

	public RemoveFeatureAttributeAction(IFeatureModelManager fmManager, List<IFeatureAttribute> attributes) {
		super(StringTable.REMOVE_SELECTED_ATTRIBUTE);
		this.fmManager = fmManager;
		this.attributes = attributes;
	}

	@Override
	public void run() {
		fmManager.editObject(this::removeAttributes, FeatureModelManager.CHANGE_ATTRIBUTES);
	}

	private void removeAttributes(IFeatureModel featureModel) {
		for (final IFeatureAttribute attribute : attributes) {
			// delete all of these recursive elements
			if (attribute.isRecursive()) {
				if (attribute.isHeadOfRecursiveAttribute()) {
					for (final IFeature feature : featureModel.getFeatures()) {
						IExtendedFeature extendedFeature = (IExtendedFeature) feature;
						for (IFeatureAttribute localAttribute : extendedFeature.getAttributes()) {
							if (attribute.getName().equals(localAttribute.getName())) {
								extendedFeature.removeAttribute(localAttribute);
							}
						}
					}
				}
			} else {
				for (final IFeature feature : featureModel.getFeatures()) {
					IExtendedFeature extendedFeature = (IExtendedFeature) feature;
					if (extendedFeature.getAttributes().contains(attribute)) {
						extendedFeature.removeAttribute(attribute);
					}
				}
			}
		}
		featureModel.fireEvent(new FeatureIDEEvent(null, EventType.FEATURE_ATTRIBUTE_CHANGED, true, FeatureUtils.getRoot(featureModel)));
	}

	@Override
	public boolean isEnabled() {
		return attributes.size() > 0;
	}

}
