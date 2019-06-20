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
package de.ovgu.featureide.fm.core.filter;

import java.util.Collection;
import java.util.HashSet;

import de.ovgu.featureide.fm.core.filter.base.Filter;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

/**
 * Filters all features that are contained in a given collection.
 *
 * @author Sebastian Krieter
 *
 * @see Filter
 */
public class HashSetFilter<T> extends HashSet<T> implements IFilter<T> {

	private static final long serialVersionUID = -2813705402751330237L;

	public HashSetFilter() {
		super();
	}

	public HashSetFilter(Collection<? extends T> c) {
		super(c);
	}

	public HashSetFilter(int initialCapacity, float loadFactor) {
		super(initialCapacity, loadFactor);
	}

	public HashSetFilter(int initialCapacity) {
		super(initialCapacity);
	}

	@Override
	public boolean isValid(T object) {
		return contains(object);
	}

}
