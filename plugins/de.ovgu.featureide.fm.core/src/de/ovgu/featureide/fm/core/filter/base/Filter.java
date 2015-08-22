/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.filter.base;

import java.util.Iterator;

/**
 * Filters elements out of a collection based on a test from one or more {@link IFilter} instances.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 * 
 * @see InverseFilter
 */
public abstract class Filter {

	/**
	 * Removes all elements from the collection that do <b>not</b> pass the filter.
	 * 
	 * @param source the collection
	 * @param predicate the filter
	 */
	public static <U, T extends U, V extends Iterable<T>> V retain(V source, IFilter<U> predicate) {
		if (source != null && predicate != null) {
			for (Iterator<T> iterator = source.iterator(); iterator.hasNext();) {
				if (!predicate.isValid(iterator.next())) {
					iterator.remove();
				}
			}
		}
		return source;
	}

	/**
	 * Removes all elements from the collection that pass the filter.
	 * 
	 * @param source the collection
	 * @param predicate the filter
	 */
	public static <U, T extends U, V extends Iterable<T>> V remove(V source, IFilter<U> predicate) {
		if (source != null && predicate != null) {
			for (Iterator<T> iterator = source.iterator(); iterator.hasNext();) {
				if (predicate.isValid(iterator.next())) {
					iterator.remove();
				}
			}
		}
		return source;
	}

}
