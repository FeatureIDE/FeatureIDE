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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.filter.ConcreteFeatureFilter;

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
	 * @param collection the collection
	 * @param filter the filter
	 */
	public static <U, T extends U> Collection<T> filter(Collection<T> collection, IFilter<U> filter) {
		if (collection != null && filter != null) {
			for (Iterator<T> iterator = collection.iterator(); iterator.hasNext();) {
				if (!filter.isValid(iterator.next())) {
					iterator.remove();
				}
			}
		}
		return collection;
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public static <T> Collection<T> filter(Collection<T> collection, Collection<IFilter<?>> filterList) {
		if (collection != null && filterList != null) {
			for (IFilter filter : filterList) {
				for (Iterator<T> iterator = collection.iterator(); iterator.hasNext();) {
					if (!filter.isValid(iterator.next())) {
						iterator.remove();
					}
				}
			}
		}
		return collection;
	}
	
	public static List<String> toString(Collection<?> collection) {
		if (collection != null) {
			final ArrayList<String> result = new ArrayList<>(collection.size());
			for (Iterator<?> iterator = collection.iterator(); iterator.hasNext();) {
				result.add(iterator.next().toString());
			}
			return result;
		}
		return Collections.emptyList();
	}

	public static <U, T extends U> List<String> toString(Collection<T> collection, IFilter<U> filter) {
		if (collection != null && filter != null) {
			final ArrayList<String> result = new ArrayList<>(collection.size());
			for (Iterator<T> iterator = collection.iterator(); iterator.hasNext();) {
				if (filter.isValid(iterator.next())) {
					result.add(iterator.next().toString());
				}
			}
			return result;
		}
		return Collections.emptyList();
	}
	
	public static final ConcreteFeatureFilter CONCRETE_FEATURE_FILTER = new ConcreteFeatureFilter();
	
	private static class FilteredIterator<U, T extends U> implements Iterator<T> {
		
		private IFilter<U> filter;
		
		private Iterator<T> collectionIterator;
		
		private T next;
		
		public FilteredIterator(Collection<T> collection, IFilter<U> filter) {
			assert (collection != null);
			assert (filter != null);
			
			this.collectionIterator = collection.iterator();
			this.filter = filter;
		}
		

		@Override
		public boolean hasNext() {
			if (!collectionIterator.hasNext())
				return false;
			else {
				this.next = collectionIterator.next();
				return filter.isValid(this.next)? true : hasNext();
			}
		}

		@Override
		public T next() {
			if (this.next == null)
				throw new NoSuchElementException();
			return this.next;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
		
	}
	
	public static <U, T extends U> Iterator<T> filteredIterator(Collection<T> collection, IFilter<U> filter) {
		if (collection != null && filter != null) {
			for (Iterator<T> iterator = collection.iterator(); iterator.hasNext();) {
				if (!filter.isValid(iterator.next())) {
					iterator.remove();
				}
			}
		}
		return collection;
	}

}
