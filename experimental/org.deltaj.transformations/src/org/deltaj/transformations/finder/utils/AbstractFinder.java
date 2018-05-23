package org.deltaj.transformations.finder.utils;

public abstract class AbstractFinder<T> {

	/**
	 * Returns the matching element or throws an exception.
	 * 
	 * @throws IllegalArgumentException
	 *             if no matching element can be found
	 */
	public T findOrThrow() {

		T element = find();
		if (element == null) {
			throw new IllegalArgumentException(String.format(
					"An element with the name '%s' could not be found.",
					element));
		}
		return element;
	}

	protected abstract T find();
}
