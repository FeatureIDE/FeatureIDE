/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.functional;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.fm.core.filter.base.IFilter;

/**
 * Common interfaces for functional style.
 * 
 * @author Marcus Pinnecke
 */
public abstract class Functional {

	/**
	 * Represents a function that takes one argument of type <b>T</b> and returns a result of type <b>R</b>.
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.3
	 */
	public static interface IFunction<T, R> {
		R invoke(T t);
	}

	/**
	 * Represents a function that takes two arguments of type <b>T</b> and <b>U</b>. It returns a result of type <b>R</b>.
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.3
	 */
	public static interface IBinaryFunction<T, U, R> {
		R invoke(T t, U u);
	}

	/**
	 * Represents a function that takes one arguments of type <b>T</b> and returns a result of the same type.
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.3
	 */
	public static class IdentityFunction<T> implements IFunction<T, T> {
		@Override
		public T invoke(T t) {
			return t;
		}
	};

	/**
	 * Represents an operation that takes one arguments of type <b>T</b> and produces no result.
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.3
	 */
	public static interface IConsumer<T> {
		void invoke(T t);
	}

	/**
	 * Represents an operation that takes no arguments but produces a result of type <b>T</b>.
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.3
	 */
	public static interface IProvider<T> {
		T invoke();
	}

	public static class NullFunction<T, U> implements IFunction<T, U> {
		@Override
		public U invoke(T t) {
			return null;
		}
	};

	public static class ToStringFunction<T> implements IFunction<T, CharSequence> {
		@Override
		public CharSequence invoke(T t) {
			return t.toString();
		}
	};

	/**
	 * Implements an iterable iterator that invokes a user-defined {@link Functional.IFunction Function} <i>f</i> of type <b>T</b> and <b>U</b> on
	 * each
	 * element that is yield by a user provided iterator <i>i</i> of type <b>T</b>. Since this is implemented using iterator logic, the application of <i>f</i>
	 * on the entire
	 * collection of element is done in a lazy fashion. Furthermore, it is guaranteed no element from the iterator <i>i</i> is removed during this process.
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	private static class MapIterator<U, T> implements Iterator<U>, Iterable<U> {

		private final IFunction<T, U> function;

		private final Iterator<T> collectionIterator;

		/**
		 * An iterable iterator that invokes a user-defined {@link Functional.IFunction Function} of type <b>T</b> and <b>U</b> on
		 * each element providing by the iterator of <b>it</b> over type <b>T</b> and returns the modified element afterwards. It is guaranteed not to remove
		 * any element from <b>it</b> during this process.
		 * 
		 * @param collection
		 * @param function
		 */
		public MapIterator(Iterable<T> it, IFunction<T, U> function) {
			assert (it != null);
			assert (function != null);

			this.collectionIterator = it.iterator();
			this.function = function;
		}

		@Override
		public boolean hasNext() {
			return collectionIterator.hasNext();
		}

		@Override
		public U next() {
			return function.invoke(collectionIterator.next());
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Iterator<U> iterator() {
			return this;
		}
	}

	/**
	 * Implements an iterable iterator that only yields elements of type <b>T</b> provided by a user-defined iterator <i>i</i> if and only if the elements
	 * satisfy a
	 * user-defined filter condition <i>c</i> over elements of type <b>U</b>. Since this is implemented using iterator logic, the evaluation of <i>c</i>
	 * on the entire collection of element is done in a lazy fashion. Furthermore, it is guaranteed not to remove any element from the iterator <i>i</i>.
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	private static class FilterIterator<U, T extends U> implements Iterator<T>, Iterable<T> {

		private final IFilter<U> filter;

		private final Iterator<T> collectionIterator;

		private T next;

		/**
		 * An iterable iterator that only yields elements of type <b>T</b> provided by a user-defined iterator <b>i</b> if and only if the elements satisfy a
		 * user-defined filter condition defined by a {@link de.ovgu.featureide.fm.core.filter.base.IFilter Filter} <b>filter</b> of type <b>U</b>.
		 * Since this is implemented using iterator logic, the evaluation of <i>c</i>
		 * on the entire collection of element is done in a lazy fashion. Furthermore, it is guaranteed not to remove any element from the iterator <i>i</i>.
		 * 
		 * @author Marcus Pinnecke
		 * @since 2.7.5
		 */
		public FilterIterator(Iterable<T> it, IFilter<U> filter) {
			assert (it != null);
			assert (filter != null);

			this.collectionIterator = it.iterator();
			this.filter = filter;
		}
		
		@Override
		public boolean hasNext() {
			while (collectionIterator.hasNext()) {
				next = collectionIterator.next();
				if (filter.isValid(next)) {
					return true;
				}
			}
			next = null;
			return false;
		}

		@Override
		public T next() {
			return this.next;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Iterator<T> iterator() {
			return this;
		}
	}

	/**
	 * Filters an object named <b>source</b> that yields elements of type <b>T</b> by a given <b>predicate</b> over <b>U</b> and transforms all qualified
	 * elements from <b>T</b> to <b>U</b>
	 * using a user-defined {@link de.ovgu.featureide.fm.core.filter.base.IFilter Filter}.
	 * This filtering is done in a lazy manner using iterator logic. Furthermore, it is guaranteed not to remove any element from the iterator <i>i</i>.
	 * </br></br>It is assumed that <b>source</b> and </b>predicate</b> are non-null. <br/>
	 * <br/>
	 * This is a <b>non-blocking</b> operation.
	 * 
	 * @param source Source of elements
	 * @param predicate Filter condition
	 * @return An iterable object that yields all qualified elements of </b>source</b>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public static <U, T extends U> Iterable<T> filter(final Iterable<T> source, final IFilter<U> predicate) {
		return new FilterIterator<U, T>(source, predicate);
	}

	/**
	 * Maps a user-defined {@link IFunction} that takes elements of type <b>T</b> and returns for each element a result of type <b>U</b> on each element of an
	 * object named <b>source</b> that yields elements of type <b>T</b>.
	 * This mapping process is done in a lazy manner using iterator logic. Furthermore, it is guaranteed not to remove any element from the iterator <i>i</i>.
	 * </br></br>It is assumed that <b>source</b> and </b>function</b> are non-null. <br/>
	 * <br/>
	 * This is a <b>non-blocking</b> operation.
	 * 
	 * @param source Source of elements
	 * @param function user-defined {@link IFunction}
	 * @return An iterable object that yields all elements of <b>source</b> after applying <b>function</b>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public static <U, T> Iterable<U> map(final Iterable<T> source, IFunction<T, U> function) {
		return new MapIterator<U, T>(source, function);
	}

	/**
	 * Converts the iterator of type <b>T</b> into an iterator of type <b>String</b> by invoking <code>toString()</code> on each element.
	 * <br/>
	 * It is guaranteed to not remove any element from the iterator. <br/>
	 * <br/>
	 * This is a <b>non-blocking</b> operation.
	 * 
	 * @param source Source of elements
	 * @return An iterable object that yields all elements of <b>source</b> after invoking <code>toString</code> on them
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public static <T> Iterable<CharSequence> mapToString(final Iterable<T> source) {
		return map(source, new ToStringFunction<T>());
	}

	/**
	 * Converts the iterator <i>i</i> of type <b>T</b> into an list of type <b>T</b> by adding each element of <i>i</i> to the result list. <br/>
	 * <br/>
	 * It is guaranteed not to remove any element from the iterator. <br/>
	 * <br/>
	 * This is a <b>blocking</b> operation.
	 * 
	 * @param source Source of elements
	 * @return A list of object that were yielded by <b>source</b>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public static <T> List<T> toList(final Iterable<T> source) {
		ArrayList<T> retval = new ArrayList<T>();
		for (T t : source) {
			retval.add(t);
		}
		return retval;
	}
	
	/**
	 * Converts the iterator <i>i</i> of type <b>T</b> into an set of type <b>T</b> by adding each element of <i>i</i> to the result set. <br/>
	 * <br/>
	 * It is guaranteed not to remove any element from the iterator. <br/>
	 * <br/>
	 * This is a <b>blocking</b> operation.
	 * 
	 * @param source Source of elements
	 * @return A list of object that were yielded by <b>source</b>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public static <T> Set<T> toSet(final Iterable<T> source) {
		HashSet<T> retval = new HashSet<T>();
		for (T t : source) {
			retval.add(t);
		}
		return retval;
	}

	/**
	 * Converts the iterator <i>i</i> of type <b>T</b> into an list of <b>Strings</b> using {@link #mapToString(Iterable)} on <b>source</b> and finally
	 * {@link #toList(Iterable)} on the result. <br/>
	 * <br/>
	 * It is guaranteed not to remove any element from the iterator. <br/>
	 * <br/>
	 * This is a <b>blocking</b> operation.
	 * 
	 * @param source Source of elements
	 * @return A list of strings that were yielded by <b>source</b>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public static <T> List<CharSequence> mapToStringList(final Iterable<T> source) {
		return toList(map(source, new ToStringFunction<T>()));
	}

}
