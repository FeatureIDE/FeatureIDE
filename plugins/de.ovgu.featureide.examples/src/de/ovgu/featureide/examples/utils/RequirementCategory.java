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
package de.ovgu.featureide.examples.utils;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * This class holds information about categrory and requirements. Is required for CommentParser.
 *
 * @author Alexander Dreiling
 */
public class RequirementCategory {

	String catName;
	Map<String, String> requirements = new HashMap<String, String>();

	public RequirementCategory(String categoryName, Map<String, String> requirements) {
		catName = categoryName;
		this.requirements = requirements;
	}

	public String getCategory() {
		return catName;
	}

	public Set<String> getPluginIds() {
		return requirements.keySet();
	}

	public String getErrorMsg(String pluginId) {
		return requirements.get(pluginId);

	}
}
