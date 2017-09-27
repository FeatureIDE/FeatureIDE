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

/**
 * Node in the statistics view to show lines of code.
 *
 * @author Schleicher Miro
 */
public class HashMapNodeTwoStrings extends AbstractSortModeNode {

	private HashMap<String, Integer> featureExtensionLOCList = new HashMap<String, Integer>();
	private final HashMap<String, Integer> count = new HashMap<String, Integer>();
	private final int side;

	public HashMapNodeTwoStrings(String description, int side, HashMap<String, Integer> extList) {
		super(description);
		featureExtensionLOCList = extList;
		this.side = side;
	}

	@Override
	protected void initChildren() {
		for (final String name : featureExtensionLOCList.keySet()) {
			if (side == 1) {
				if (!count.containsKey(name.split("#")[0])) {
					count.put(name.split("#")[0], featureExtensionLOCList.get(name));
				} else {
					count.put(name.split("#")[0], count.get(name.split("#")[0]) + featureExtensionLOCList.get(name));
				}
			} else if (side == 2) {
				if (!count.containsKey(name.split("#")[1])) {
					count.put(name.split("#")[1], featureExtensionLOCList.get(name));
				} else {
					count.put(name.split("#")[1], count.get(name.split("#")[1]) + featureExtensionLOCList.get(name));
				}
			}
		}

		for (final String name : count.keySet()) {
			addChild(new HashMapNodeTwoStringsSub(name, count.get(name), featureExtensionLOCList, side));
		}

	}

}
