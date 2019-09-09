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

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;

/**
 * 
 * Extension of a selectable feature (Features in the context of a configuiration) Attaches map with attribute values which were changed in the configuration
 * 
 * @author Chico Sundermann
 */

public class ExtendedSelectableFeature extends SelectableFeature {

	// Store name and value as string
	private Map<String, String> configurableAttributes = new HashMap<String, String>();

	public ExtendedSelectableFeature(IFeature feature) {
		super(feature);
	}

	public ExtendedSelectableFeature(IFeature feature, Map<String, String> confAtt) {
		super(feature);
		this.configurableAttributes = confAtt;
	}

	/**
	 *
	 * @return Map<Name of the attribute, value of the attribute>
	 */
	public Map<String, String> getConfigurableAttributes() {
		return configurableAttributes;
	}

	/**
	 * Adds a name/ value pair to the configured attributes map
	 * 
	 * @param name
	 * @param value
	 */
	public void addConfigurableAttribute(String name, String value) {
		configurableAttributes.put(name, value);
	}

	@Override
	public void cloneProperties(SelectableFeature feat) {
		if (feat instanceof ExtendedSelectableFeature) {
			configurableAttributes = ((ExtendedSelectableFeature) feat).getConfigurableAttributes();
		}
	}

}
