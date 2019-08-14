/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.Random;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.ovgu.featureide.fm.core.filter.base.AndFilter;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

/**
 * Common interfaces for functional style.
 *
 * @author Marcus Pinnecke
 */
public abstract class Functional {

	/**
	 * Convenience function to invoke {@link Object#toString()} on the input parameter.
	 *
	 * @param <T> element class
	 *
	 * @see Functional#mapToString(Iterable)
	 * @see Functional.ToCharSequenceFunction
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 */
	public static class ToStringFunction<T> implements Function<T, String> {

		@Override
		public String apply(T t) {
			return t.toString();
		}
	};

	/**
	 * Convenience function to invoke {@link Object#toString()} on the input parameter. Afterwards the resulting string is converted to an instance of
	 * {@link CharSequence}.
	 *
	 * @param <T> element class
	 *
	 * @see Functional.ToStringFunction
	 * @see Functional#mapToString(Iterable)
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static class ToCharSequenceFunction<T> implements Function<T, CharSequence> {

		@Override
		public CharSequence apply(T t) {
			return t.toString();
		}
	};

	private static class DefaultIterable<U, T extends U> implements Iterable<T> {

		private final Iterator<T> iterator;

		public DefaultIterable(Iterator<T> iterator) {
			this.iterator = iterator;
		}

		@Override
		public Iterator<T> iterator() {
			return iterator;
		}
	}

	/**
	 * Implements an iterable iterator that invokes a user-defined {@link Functional.Function Function} <i>f</i> of type <b>T</b> and <b>U</b> on each element
	 * that is yield by a user provided iterator <i>i</i> of type <b>T</b>. Since this is implemented using iterator logic, the application of <i>f</i> on the
	 * entire collection of element is done in a lazy fashion. Furthermore, it is guaranteed no element from the iterator <i>i</i> is removed during this
	 * process.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	private static class MapIterator<U, T> implements Iterator<U>, Iterable<U> {

		private final Function<T, U> function;

		private final Iterator<T> collectionIterator;

		/**
		 * An iterable iterator that invokes a user-defined {@link Function} of type <b>T</b> and <b>U</b> on each element providing by the iterator of
		 * <b>it</b> over type <b>T</b> and returns the modified element afterwards. It is guaranteed not to remove any element from <b>it</b> during this
		 * process.
		 *
		 * @param it the iterable
		 * @param function the function
		 */
		public MapIterator(Iterable<T> it, Function<T, U> function) {
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
			return function.apply(collectionIterator.next());
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
	 * satisfy a user-defined filter condition <i>c</i> over elements of type <b>U</b>. Since this is implemented using iterator logic, the evaluation of
	 * <i>c</i> on the entire collection of element is done in a lazy fashion. Furthermore, it is guaranteed not to remove any element from the iterator
	 * <i>i</i>.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	private static class FilterIterator<U, T extends U> implements Iterator<T>, Iterable<T> {

		private final IFilter<U> filter;

		private final Iterator<T> collectionIterator;

		private T next;

		/**
		 * An iterable iterator that only yields elements of type <b>T</b> provided by a user-defined iterator <b>i</b> if and only if the elements satisfy a
		 * user-defined filter condition defined by a {@link de.ovgu.featureide.fm.core.filter.base.IFilter Filter} <b>filter</b> of type <b>U</b>. Since this
		 * is implemented using iterator logic, the evaluation of <i>c</i> on the entire collection of element is done in a lazy fashion. Furthermore, it is
		 * guaranteed not to remove any element from the iterator <i>i</i>.
		 *
		 * @param it the iterable
		 * @param filter the filter
		 *
		 * @author Marcus Pinnecke
		 * @since 3.0
		 */
		public FilterIterator(Iterable<T> it, IFilter<U> filter) {
			this(it.iterator(), filter);
		}

		public FilterIterator(Iterator<T> it, IFilter<U> filter) {
			assert (it != null);
			assert (filter != null);

			this.collectionIterator = it;
			this.filter = filter;
		}

		@Override
		public boolean hasNext() {
			while (collectionIterator.hasNext()) {
				next = collectionIterator.next();
				if (filter.test(next)) {
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
	 * elements from <b>T</b> to <b>U</b> using a user-defined {@link de.ovgu.featureide.fm.core.filter.base.IFilter Filter}. This filtering is done in a lazy
	 * manner using iterator logic. Furthermore, it is guaranteed not to remove any element from the iterator <i>i</i>. <br> <br> It is assumed that
	 * <b>source</b> and <b>predicate</b> are non-null. <br> <br> This is a <b>non-blocking</b> operation.
	 *
	 * @param source Source of elements
	 * @param predicate Filter condition
	 * @param <U> mapped element class
	 * @param <T> element class
	 * @return An iterable object that yields all qualified elements of <b>source</b>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <U, T extends U> Iterable<T> filter(final Iterable<T> source, final IFilter<U> predicate) {
		return predicate == null ? source : new FilterIterator<U, T>(source, predicate);
	}

	public static <U, T extends U> Iterable<T> filter(final Iterable<T> source, final List<IFilter<U>> predicate) {
		return predicate == null ? source : new FilterIterator<U, T>(source, new AndFilter<U>(predicate));
	}

	@SafeVarargs
	public static <U, T extends U> Iterable<T> filter(final Iterable<T> source, final IFilter<U>... predicate) {
		return filter(source, Arrays.asList(predicate));
	}

	public static <U, T extends U> Iterable<T> filter(final Iterator<T> source, final IFilter<U> predicate) {
		return predicate == null ? new DefaultIterable<>(source) : new FilterIterator<>(source, predicate);
	}

	/**
	 * Maps a user-defined {@link Function} that takes elements of type <b>T</b> and returns for each element a result of type <b>U</b> on each element of an
	 * object named <b>source</b> that yields elements of type <b>T</b>. This mapping process is done in a lazy manner using iterator logic. Furthermore, it is
	 * guaranteed not to remove any element from the iterator <i>i</i>. <br> <br> It is assumed that <b>source</b> and <b>function</b> are non-null. <br> <br>
	 * This is a <b>non-blocking</b> operation.
	 *
	 * @param source Source of elements
	 * @param function user-defined {@link Function}
	 * @param <U> mapped element class
	 * @param <T> element class
	 * @return An iterable object that yields all elements of <b>source</b> after applying <b>function</b>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <U, T> Iterable<U> map(final Iterable<T> source, Function<T, U> function) {
		return new MapIterator<>(source, function);
	}

	/**
	 * Converts the iterator of type <b>T</b> into an iterator of type <b>String</b> by invoking <code>toString()</code> on each element. <br> It is guaranteed
	 * to not remove any element from the iterator. <br> <br> This is a <b>non-blocking</b> operation.
	 *
	 * @param source Source of elements
	 * @param <T> element class
	 * @return An iterable object that yields all elements of <b>source</b> after invoking <code>toString</code> on them
	 *
	 * @see Functional.ToStringFunction
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T> Iterable<CharSequence> mapToString(final Iterable<T> source) {
		return map(source, new ToCharSequenceFunction<T>());
	}

	public static <T> Collection<T> toCollection(Iterable<T> elements) {
		return (elements instanceof Collection) ? ((Collection<T>) elements) : Functional.toList(elements);
	}

	/**
	 * Converts the iterator <i>i</i> of type <b>T</b> into a list of type <b>T</b> by adding each element of <i>i</i> to the result list. <br> <br> It is
	 * guaranteed not to remove any element from the iterator. <br> <br> This is a <b>blocking</b> operation. The resulting list <b>is not modifiable</b>
	 *
	 * @param source Source of elements
	 * @param <T> element class
	 * @return A list of object that were yielded by <b>source</b>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T> List<T> toList(final Iterable<T> source) {
		return collect(source, new ArrayList<>());
	}

	/**
	 * Converts the iterator <i>i</i> of type <b>T</b> into a set of type <b>T</b> by adding each element of <i>i</i> to the result set. <br> <br> It is
	 * guaranteed not to remove any element from the iterator. <br> <br> This is a <b>blocking</b> operation. The resulting set <b>is not modifiable</b>.
	 *
	 * @param source Source of elements
	 * @param <T> element class
	 * @return A list of object that were yielded by <b>source</b>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T> Set<T> toSet(final Iterable<T> source) {
		return collect(source, new HashSet<>());
	}

	private static <T, C extends Collection<T>> C collect(final Iterable<T> source, C collection) {
		source.forEach(collection::add);
		return collection;
	}

	public static <T, R> List<R> mapToList(final Iterable<T> source, IFilter<T> filter, Function<T, R> mapFunction) {
		return Functional.toList(Functional.map(Functional.filter(source, filter), mapFunction));
	}

	public static <T, R> List<R> mapToList(final Iterable<T> source, Function<T, R> mapFunction) {
		return Functional.toList(Functional.map(source, mapFunction));
	}

	public static <T> List<T> filterToList(final Iterable<T> source, IFilter<T> filter) {
		return Functional.toList(Functional.filter(source, filter));
	}

	/**
	 * Converts the iterator <i>source</i> of type <b>T</b> into a list of <b>Strings</b> using {@link #mapToString(Iterable)} on <b>source</b> and finally
	 * {@link #toList(Iterable)} on the result. <br> <br> It is guaranteed not to remove any element from the iterator. <br> <br> This is a <b>blocking</b>
	 * operation.
	 *
	 * @param source Source of elements
	 * @param <T> element class
	 * @return A collection of strings that were yielded by <b>source</b>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T> List<String> mapToStringList(final Iterable<T> source) {
		return toList(map(source, new ToStringFunction<T>()));
	}

	/**
	 * Converts the iterator <i>source</i> of type <b>T</b> into a set of <b>Strings</b> using {@link #mapToString(Iterable)} on <b>source</b> and finally
	 * {@link #toSet(Iterable)} on the result. <br> <br> It is guaranteed not to remove any element from the iterator. <br> <br> This is a <b>blocking</b>
	 * operation.
	 *
	 * @param source Source of elements
	 * @param <T> element class
	 * @return A collection of strings that were yielded by <b>source</b>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T> Set<String> mapToStringSet(final Iterable<T> source) {
		return toSet(map(source, new ToStringFunction<T>()));
	}

	/**
	 * Joins the elements of type <b>T</b> in <code>source</code> using <code>delimiter</code> as the delimiting element between a pair of elements from
	 * <code>source</code> into a combined object of type <b>R</b>. The method first constructs a new instance of <b>R</b> as the <i>result</i> using the
	 * <code>newInstanceOfR</code> parameter. Afterwards <code>source</code> is converted to a list of type <b>T</b>. For each element in this list the function
	 * parameter <code>concat</code> is invoked with <i>result</i> as the first parameter and the current element of the list as second parameter. For each pair
	 * of elements, <code>concat</code> is invoked again to add the delimiter. <br> <br> <b>Example</b><br> The convenience method
	 * {@link Functional#join(Iterable, String, Function)} which takes the elements yielded by <code>source</code> and joins these elements into a string is
	 * implemented using the general method {@link Functional#join(Iterable, Object, Supplier, Function, BiFunction)}:. <code> &lt;T&gt; String
	 * join(Iterable&lt;T&gt; source, String delimiter, Function&lt;T, String&gt; convert) { return join(source, delimiter, new Supplier&lt;String&gt;() {
	 * String invoke() { return ""; } }, convert, new BiFunction&lt;String, String, String&gt;() { String invoke(String t, String u) { return t + u; } }); }
	 * </code> <br>
	 *
	 * @param <T> The type of elements whose iterable source should be joined to an object of type <b>R</b>
	 * @param <R> The targeted type of the joined elements of <code>source</code>
	 * @param source The input source of elements from type <b>T</b>
	 * @param delimiter delimiter The delimiting element between elements of <code>source</code>, after each element of <code>source</code> was converted to
	 *        type <b>R</b>
	 * @param newInstanceOfR Constructs a new instance of type <b>R</b> each time it is invoked
	 * @param convert A function which converts an object of type <b>T</b> to type <b>R</b>
	 * @param concat A binary function which takes two objects of type <b>T</b> and concats them to a single object using the delimiter <code>delimiter</code>.
	 * @return Joined version of <code>source</code> using <code>delimiter</code>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T, R> R join(final Iterable<T> source, final R delimiter, final Supplier<R> newInstanceOfR, final Function<T, R> convert,
			final BiFunction<R, R, R> concat) {
		R result = newInstanceOfR.get();
		final List<T> list = toList(source);
		for (int i = 0; i < list.size(); i++) {
			result = concat.apply(result, convert.apply(list.get(i)));
			if ((i + 1) < list.size()) {
				result = concat.apply(result, delimiter);
			}
		}
		return result;
	}

	/**
	 * Takes the elements yielded by <code>source</code> and joins these elements into a string. The parameter <code>delimiter</code> is the delimiting element
	 * between two elements in the string. Since <code>source</code> is a iterable over a arbitrary type <b>T</b>, the parameter <code>convert</code> of type
	 * <code>Function</code> deals with the converting from <b>T</b> to <b>String</b>. <br> <br> <b>Example</b><br> In the following example, the list of double
	 * values <code>{7.7534, 2.322, 14.532}</code> is joined using {@link Functional#join(Iterable, String, Function)}. Each value is rounded to one decimal
	 * place. The entire rounded values are then joined using a whitespace. The result <code>7,8 2,4 14,6</code> is printed to standard out. <code> final
	 * DecimalFormat df = new DecimalFormat("#.#"); df.setRoundingMode(RoundingMode.CEILING); Function&lt;Double, String&gt; roundDoubleToString = new
	 * Function&lt;Double, String&gt;() { &#64;Override public String invoke(Double input) { return df.format(input.doubleValue()).toString(); } };
	 *
	 * List&lt;Double&gt; list = new ArrayList&lt;&gt;(Arrays.asList(new Double[] {7.7534, 2.322, 14.532})); String joinedValues = Functional.join(list, " ",
	 * roundDoubleToString); System.out.println(joinedValues); </code> It is good practise to store multiple occurrences of the function <code>convert</code>
	 * into a static member of some class. The example above can be than reduced to the following. <br> <br> <code> List&lt;Double&gt; list = new
	 * ArrayList&lt;&gt;(Arrays.asList(new Double[] {7.7534, 2.322, 14.532})); String joinedValues = Functional.join(list, " ", ROUND_DOUBLE_TO_STRING);
	 * System.out.println(joinedValues); </code>
	 *
	 * @param <T> type of the elements in <code>source</code>
	 * @param source The input source of elements from type <b>T</b>
	 * @param delimiter The delimiting string between elements of <code>source</code>
	 * @param convert A function to convert from <b>T</b> to <b>String</b>
	 * @return A string representation of the joined elements of <code>source</code> using <code>delimited</code> as delimiting string
	 *
	 * @see Functional#join(Iterable, Object, Supplier, Function, BiFunction)
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T> String join(final Iterable<T> source, final String delimiter, final Function<T, String> convert) {
		return join(source, delimiter, new Supplier<String>() {

			@Override
			public String get() {
				return "";
			}
		}, convert, new BiFunction<String, String, String>() {

			@Override
			public String apply(String t, String u) {
				return t + u;
			}

		});
	}

	/**
	 * Checks if the two given iterables <code>lhs</code> and <code>rhs</code> are equal. Moreover, the elements from both iterables are converted from origin
	 * type <b>T</b> to target type <b>U</b> using the parameter <code>map</code>. The methods maps <code>map</code> on both <code>lhs</code> and
	 * <code>rhs</code> in order to produce a {@link Set} of type <b>U</b> for both. Both sets are than compared using {@link Set#equals(Object)}.
	 *
	 * @param <T> the elements of both iterables <code>lhs</code> and <code>rhs</code>
	 * @param <U> an intermediate type to check the equality.
	 * @param lhs Iterable which should be checked of equality to <code>rhs</code>
	 * @param rhs Iterable which should be checked of equality to <code>lhs</code>
	 * @param map Converts elements from <b>T</b> to <b>U</b>
	 * @return <b>true</b> if the elements in <code>lhs</code> are also in <b>rhs</b> and vice versa, otherwise <b>false</b>.<br> <u><b>Note on
	 *         duplicates</b></u>: Duplicates in both <code>lhs</code> and <code>rhs</code> are eliminated <u>before</u> the test of equality.
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 */
	public static <T, U> boolean equals(final Iterable<T> lhs, final Iterable<T> rhs, final Function<T, U> map) {
		final Set<U> left = Functional.toSet(Functional.map(lhs, map));
		final Set<U> right = Functional.toSet(Functional.map(rhs, map));
		return left.equals(right);
	}

	/**
	 * Checks whenever <code>iterable</code> is empty or not by calling <code>iterable.iterator().hasNext()</code>
	 *
	 * @author Marcus Pinnecke
	 * @since 3.0
	 *
	 * @param <T> type of elements in <code>iterable</code>
	 * @param iterable iterable collection of type <b>T</b>
	 *
	 * @return <b>true</b> if <code>iterable</code> is empty, otherwise <b>false</b>
	 */
	public static <T> boolean isEmpty(Iterable<T> iterable) {
		return !iterable.iterator().hasNext();
	}

	public static <T> Integer[] getSortedIndex(final List<T> list, final Comparator<T> comparator) {
		final Integer[] index = getIndex(list.size());
		Arrays.sort(index, new Comparator<Integer>() {

			@Override
			public int compare(Integer o1, Integer o2) {
				return comparator.compare(list.get(o1), list.get(o2));
			}
		});
		return index;
	}

	public static Integer[] getRandomizedIndex(int size) {
		return getRandomizedIndex(size, new Random());
	}

	public static Integer[] getRandomizedIndex(int size, Random random) {
		final Integer[] index = getIndex(size);
		Collections.shuffle(Arrays.asList(index), random);
		return index;
	}

	public static Integer[] getIndex(int size) {
		final Integer[] index = new Integer[size];
		for (int i = 0; i < index.length; i++) {
			index[i] = i;
		}
		return index;
	}

	public static <T> List<T> removeNull(List<T> oldList) {
		if (oldList == null) {
			return null;
		} else {
			return oldList.stream().filter(Objects::nonNull).collect(Collectors.toList());
		}
	}

}
