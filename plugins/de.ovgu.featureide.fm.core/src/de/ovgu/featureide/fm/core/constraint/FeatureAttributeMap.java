/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

/**
 * Maps a {@link FeatureAttribute} to its name and feature.
 * 
 * @author Sebastian Krieter
 */
public class FeatureAttributeMap<T> {

	private Map<String, Map<String, FeatureAttribute<T>>> attrs = new HashMap<String, Map<String, FeatureAttribute<T>>>();

	public boolean hasAttribute(String featureName, String attributeName) {
		return attrs.containsKey(attributeName) && attrs.get(attributeName).containsKey(featureName);
	}

	public boolean hasAttribute(FeatureAttribute<T> fa) {
		return hasAttribute(fa.getFeatureName(), fa.getAttributeName());
	}

	public FeatureAttribute<T> getAttribute(String featureName, String attributeName) {
		return hasAttribute(featureName, attributeName) ? attrs.get(attributeName).get(featureName) : null;
	}

	public void setAttribute(String featureName, String attributeName, T value) {
		if (!attrs.containsKey(attributeName))
			attrs.put(attributeName, new HashMap<String, FeatureAttribute<T>>());
		
		attrs.get(attributeName).put(featureName, new FeatureAttribute<T>(attributeName, featureName, value));
	}

	public void setAttribute(FeatureAttribute<T> fa) {
		if (!attrs.containsKey(fa.getAttributeName()))
			attrs.put(fa.getAttributeName(), new HashMap<String, FeatureAttribute<T>>());
		
		attrs.get(fa.getAttributeName()).put(fa.getFeatureName(),fa);
	}

	public Collection<FeatureAttribute<T>> getAttributes(String attributeName) {
		return attrs.get(attributeName).values();
	}
}
