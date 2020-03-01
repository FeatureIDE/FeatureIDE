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
package de.ovgu.featureide.fm.attributes.view.labelprovider;

import java.util.HashMap;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.config.ExtendedSelectableFeature;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;

/**
 * Label provider for the value attribute.
 * 
 * @author Joshuas Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeValueColumnLabelProvider extends FeatureAttributeColumnLabelProvider {

	public FeatureAttributeValueColumnLabelProvider(HashMap<String, Image> cachedImages, FeatureAttributeView view) {
		super(cachedImages, view);
	}

	@Override
	public String getText(Object element) {
		if ((element instanceof IFeature) || (element instanceof String)) {
			return "-";
		} else if (element instanceof IFeatureAttribute) {
			final IFeatureAttribute attribute = (IFeatureAttribute) element;
			if (view.getCurrentEditor() instanceof ConfigurationEditor) {
				Configuration config = ((ConfigurationEditor) view.getCurrentEditor()).getConfigurationManager().getVarObject();
				for (SelectableFeature feat : config.getFeatures()) {
					if (feat.getFeature().getName().equals(attribute.getFeature().getName())) {
						if (feat instanceof ExtendedSelectableFeature) {
							ExtendedSelectableFeature extSelectable = (ExtendedSelectableFeature) feat;
							Object value = extSelectable.getAttributeValue(attribute);
							if (value != null) {
								return extSelectable.getAttributeValue(attribute).toString();
							} else {
								return "";
							}
						}
					}
				}
			}
			if (attribute.getValue() != null) {
				return attribute.getValue().toString();
			}
			return "";
		}
		return "null";
	}
}
