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
package de.ovgu.featureide.core.signature.filter;

import java.util.Collection;
import java.util.Iterator;

public abstract class Filter {

	public static <U, T extends U> void filter(Collection<T> collection, IFilter<U> filter) {
		if (collection != null && filter != null) {
			for (Iterator<T> iterator = collection.iterator(); iterator.hasNext();) {
				if (!filter.isValid(iterator.next())) {
					iterator.remove();
				}
			}
		}
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static <T> void filter(Collection<T> collection, Collection<IFilter<?>> filterList) {
		if (collection != null && filterList != null) {
			for (IFilter filter : filterList) {
				for (Iterator<T> iterator = collection.iterator(); iterator.hasNext();) {
					if (!filter.isValid(iterator.next())) {
						iterator.remove();
					}
				}
			}
		}
	}

}
