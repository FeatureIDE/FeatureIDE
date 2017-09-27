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
package de.ovgu.featureide.fm.core.filter.base;

import java.util.ArrayList;
import java.util.Collection;

/**
 * Returns the disjunction of multiple {@link IFilter}s.
 *
 * @author Sebastian Krieter
 *
 * @see Filter
 */
public class OrFilter<T> extends ArrayList<IFilter<T>> implements IFilter<T> {

	private static final long serialVersionUID = 1L;

	public OrFilter() {
		super();
	}

	public OrFilter(Collection<? extends IFilter<T>> c) {
		super(c);
	}

	public OrFilter(int initialCapacity) {
		super(initialCapacity);
	}

	@Override
	public boolean isValid(T object) {
		for (final IFilter<T> filter : this) {
			if (filter.isValid(object)) {
				return true;
			}
		}
		return false;
	}

}
