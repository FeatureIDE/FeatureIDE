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
package de.ovgu.featureide.fm.attributes.config;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

public class ExtendedSelectableFeature extends SelectableFeature {

	// Store name and value as string
	private Map<String, String> configurableAttributes = new HashMap<String, String>();

	public ExtendedSelectableFeature(IFeature feature) {
		super(feature);
	}

	public ExtendedSelectableFeature(ExtendedSelectableFeature copy) {
		super(copy.getFeature());
		configurableAttributes = new HashMap<String, String>(copy.configurableAttributes);
	}

	public ExtendedSelectableFeature(IFeature feature, Map<String, String> confAtt) {
		super(feature);
		this.configurableAttributes = confAtt;
	}

	public Map<String, String> getConfigurableAttributes() {
		return configurableAttributes;
	}

	public boolean hasAttributeWithConfiguredValue(IFeatureAttribute att) {
		return configurableAttributes.containsKey(att.getName());
	}

	public boolean hasAttributeWithConfiguredValue(String attName) {
		return configurableAttributes.containsKey(attName);
	}

	public void addConfigurableAttribute(String name, String value) {
		configurableAttributes.put(name, value);
	}

	public Object getAttributeValue(IFeatureAttribute att) {
		if (hasAttributeWithConfiguredValue(att)) {
			return configurableAttributes.get(att.getName());
		} else {
			return att.getValue();
		}
	}

	public Object getAttributeDefaultValue(String attName) {
		ExtendedFeature feat = ((ExtendedFeature) getFeature());
		for (IFeatureAttribute att : feat.getAttributes()) {
			if (att.getName().equals(attName)) {
				return att.getValue();
			}
		}
		return null;
	}

	public Object getAttributeValueByName(String attName) {
		if (hasAttributeWithConfiguredValue(attName)) {
			return configurableAttributes.get(attName);
		} else {
			return getAttributeDefaultValue(attName);
		}
	}

	public void removeConfigurableAttribute(IFeatureAttribute att) {
		if (hasAttributeWithConfiguredValue(att)) {
			configurableAttributes.remove(att.getName());
		}
	}

}
