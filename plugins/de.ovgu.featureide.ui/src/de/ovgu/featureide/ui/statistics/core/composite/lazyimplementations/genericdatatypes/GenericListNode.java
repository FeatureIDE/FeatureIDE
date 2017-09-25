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

import java.util.List;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Convenience-class. Node which is sorted by default which lazily initializes it's children. A children has it's String-representation as description. The
 * default value of this node is the list's size.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class GenericListNode<T> extends AbstractSortModeNode {

	private final List<T> list;

	/**
	 * @param description
	 * @param value
	 * @param list
	 */
	public GenericListNode(String description, List<T> list) {
		super(description, list.size());
		this.list = list;
		setSorted(true);
	}

	@Override
	protected void initChildren() {
		for (final T element : list) {
			addChild(new Parent(element.toString()));
		}
		value = list.size();
	}
}
