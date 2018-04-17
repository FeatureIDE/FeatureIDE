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

import static de.ovgu.featureide.fm.core.localization.StringTable.DOUBLE_CLICK_TO_SORT_BY_VALUE_IN_DESCENDING_ORDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOUBLE_CLICK_TO_SORT_IN_ALPHABETICAL_ORDER;

import java.util.Collections;
import java.util.Comparator;

import de.ovgu.featureide.ui.statistics.core.composite.IToolTip;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.ui.helper.TreeClickListener;

/**
 * Implements a second sorting-order. If {@link AbstractSortModeNode#sortByValue} is true, the imminent child nodes are sorted by their value instead of being
 * sorted alphabetically. In this implementation the {@link TreeClickListener} is responsible for changing this.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public abstract class AbstractSortModeNode extends LazyParent implements IToolTip {

	protected boolean sortByValue = false;

	public AbstractSortModeNode(String description, Object value) {
		super(description, value);
		setSorted(true);
	}

	public AbstractSortModeNode(String description) {
		super(description);
		setSorted(true);
	}

	public boolean isSortByValue() {
		return sortByValue;
	}

	public void setSortByValue(boolean sortByValue) {
		this.sortByValue = sortByValue;
	}

	@Override
	protected void sortChildren() {
		if (sortByValue) {
			Collections.sort(children, new Comparator<Parent>() {

				@Override
				public int compare(Parent o1, Parent o2) {
					if (o1.getValue() == null) {
						if ((o1.getDescription() != null) && (o2.getDescription() != null)) {
							final int i1 = o1.getDescription().lastIndexOf(": ");
							final int i2 = o2.getDescription().lastIndexOf(": ");
							if ((i1 > -1) && (i2 > -1)) {
								return o2.getDescription().substring(i2).compareTo(o1.getDescription().substring(i1));
							}
						}
					} else {
						return ((Integer) o2.getValue()) - ((Integer) o1.getValue());
					}
					return 0;
				}
			});
		} else {
			Collections.sort(children, new Comparator<Parent>() {

				@Override
				public int compare(Parent o1, Parent o2) {
					return o1.getDescription().compareTo(o2.getDescription());
				}
			});
		}
	}

	@Override
	public String getToolTip() {
		if (hasChildren()) {
			if (sortByValue) {
				return DOUBLE_CLICK_TO_SORT_IN_ALPHABETICAL_ORDER;
			}
			return DOUBLE_CLICK_TO_SORT_BY_VALUE_IN_DESCENDING_ORDER;
		}
		return null;
	}

}
