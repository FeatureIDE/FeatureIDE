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

import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Convenience class for simply displaying {@link HashMap}s in a {@link TreeViewer}. Autosorted with two different sorting-types.
 *
 * @see AbstractSortModeNode
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class HashMapNode extends AbstractSortModeNode {

	private final HashMap<String, Integer> countMap;

	/**
	 * @param description
	 * @param value
	 * @param countMap
	 */
	public HashMapNode(String description, Object value, HashMap<String, Integer> countMap) {
		super(description, value);
		this.countMap = countMap;
		setSorted(true);
	}

	@Override
	public void initChildren() {
		if (children.isEmpty()) {
			for (final String name : countMap.keySet()) {
				addChild(new Parent(name, countMap.get(name)));
			}
		}
	}

}
