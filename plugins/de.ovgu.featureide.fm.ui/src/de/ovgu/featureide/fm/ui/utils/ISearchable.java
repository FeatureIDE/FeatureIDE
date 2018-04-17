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
package de.ovgu.featureide.fm.ui.utils;

import java.util.Iterator;

/**
 * Interface for views and editors that implement search functionality.
 *
 * @author Sebastian Krieter
 */
public interface ISearchable<T> {

	/**
	 * Checks whether an element matches the search string.
	 *
	 * @param element The current element of the view.
	 * @param searchString The string that should be searched for.
	 *
	 * @return {@code true} if the element matches the search string, {@code false} otherwise.
	 */

	boolean matches(T element, String searchString);

	/**
	 * @return {@link Iterator} for the elements' class.
	 */
	Iterator<T> createIterator();

	/**
	 * Handles the search result. Dependent on the actual implementation reveals, selects, or highlights the matching element in the view.
	 *
	 * @param searchResult The found element.
	 */
	void found(T searchResult);

}
