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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes;

import java.util.HashMap;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Node in the statistics view to show lines of code.<br> Creates each entry for features resp. file extenstions.
 *
 * @author Schleicher Miro
 */
public class HashMapNodeTwoStringsSub extends AbstractSortModeNode {

	private final HashMap<String, Integer> featureExtensionLOCList, count;
	private final String name;
	private final int side;

	public HashMapNodeTwoStringsSub(String name, Integer integer, HashMap<String, Integer> featureExtensionLOCList, int side) {
		super(name, integer);
		this.featureExtensionLOCList = featureExtensionLOCList;
		count = new HashMap<String, Integer>();
		this.name = name;
		this.side = side;
	}

	@Override
	protected void initChildren() {

		for (final String tempName : featureExtensionLOCList.keySet()) {
			if ((side == 1) && tempName.split("#")[0].equals(name)) {
				if (!count.containsKey(tempName.split("#")[1])) {
					count.put(tempName.split("#")[1], featureExtensionLOCList.get(tempName));
				} else {
					count.put(tempName.split("#")[1], count.get(tempName.split("#")[1]) + featureExtensionLOCList.get(tempName));
				}
			} else if ((side == 2) && tempName.split("#")[1].equals(name)) {
				if (!count.containsKey(tempName.split("#")[0])) {
					count.put(tempName.split("#")[0], featureExtensionLOCList.get(tempName));
				} else {
					count.put(tempName.split("#")[0], count.get(tempName.split("#")[0]) + featureExtensionLOCList.get(tempName));
				}
			}
		}

		for (final String key : count.keySet()) {
			addChild(new Parent(key, count.get(key)));
		}

	}

}
