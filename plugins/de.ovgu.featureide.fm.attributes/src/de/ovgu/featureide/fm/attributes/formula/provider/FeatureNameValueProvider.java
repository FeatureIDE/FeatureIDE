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
package de.ovgu.featureide.fm.attributes.formula.provider;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.attributes.AttributeUtils;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

public class FeatureNameValueProvider implements FormulaValueProvider {

	IFeatureModel model;
	private Double defaultValue;

	public FeatureNameValueProvider(IFeatureModel model, Double defaultValue) {
		this.model = model;
		this.defaultValue = defaultValue;
	}

	@Override
	public Map<String, Double> getValues(Object obj, String[] values) {
		Set<String> keySet = new HashSet<>(Arrays.asList(values));
		String name = (String) obj;
		IExtendedFeature ext = (IExtendedFeature) model.getFeature(name);
		Map<String, Double> result = new HashMap<>();
		for (String key : keySet) {
			result.put(key, defaultValue);
		}
		for (IFeatureAttribute att : ext.getAttributes()) {
			if (keySet.contains(att.getName())) {
				if (att.getType().equals(FeatureAttribute.BOOLEAN)) {
					result.put(att.getName(), AttributeUtils.getBooleanValueAsDouble(att, defaultValue));
				} else {
					result.put(att.getName(), AttributeUtils.getDoubleValue(att, defaultValue));
				}

			}
		}
		return result;
	}

	@Override
	public Map<String, String> getUnits(Object obj, String[] values) {
		Set<String> keySet = new HashSet<>(Arrays.asList(values));
		String name = (String) obj;
		IExtendedFeature ext = (IExtendedFeature) model.getFeature(name);
		Map<String, String> result = new HashMap<>();
		for (IFeatureAttribute att : ext.getAttributes()) {
			if (keySet.contains(att.getName())) {
				result.put(att.getName(), att.getUnit());
			}
		}
		return result;
	}

	@Override
	public Double getDefaultValue() {
		return defaultValue;
	}

}
