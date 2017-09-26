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
package de.ovgu.featureide.fm.ui.views.outline.custom;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.jface.viewers.ITreeContentProvider;

import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;

/**
 * Abstract class that implements the ITreeContentProvider interface for the outline and enhances it with filter methods
 *
 * @author Christopher Sontag
 */
public abstract class OutlineTreeContentProvider implements ITreeContentProvider {

	private final Set<IOutlineFilter> filters = new HashSet<>();

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getElements(java.lang.Object)
	 */
	@Override
	public abstract Object[] getElements(Object inputElement);

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getChildren(java.lang.Object)
	 */
	@Override
	public abstract Object[] getChildren(Object parentElement);

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getParent(java.lang.Object)
	 */
	@Override
	public abstract Object getParent(Object element);

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#hasChildren(java.lang.Object)
	 */
	@Override
	public abstract boolean hasChildren(Object element);

	// add filter to filter set
	public void addFilter(IOutlineFilter filter) {
		filters.add(filter);
	}

	// remove filter from filter set
	public void removeFilter(IOutlineFilter filter) {
		for (final IOutlineFilter f : filters) {
			if (f.getName().equals(filter.getName())) {
				filters.remove(f);
			}
		}
	}

	public void removeAllFilters() {
		filters.clear();
	}

	public boolean hasFilter(IOutlineFilter filter) {
		for (final IOutlineFilter f : filters) {
			if (f.getName().equals(filter.getName())) {
				return true;
			}
		}
		return false;
	}

	// apply all filters from filter set
	protected Object[] filter(Object[] obj) {
		for (final IOutlineFilter filter : filters) {
			obj = filter.filter(obj);
		}
		return obj;
	}

}
