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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.init;

import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;

import javax.annotation.Nonnull;

public class LibraryManager {

	private static List<ILibrary> libraries = new ArrayList<>();

	/**
	 * Deregister and uninstall all previously registered libraries.
	 */
	public static synchronized void deregisterLibraries() {
		for (final ILibrary library : libraries) {
			if (library != null) {
				library.uninstall();
			}
		}
		libraries.clear();
	}

	/**
	 * Register and install a library.
	 *
	 * @param library the library to register.
	 *
	 * @see #deregisterLibraries()
	 * @see #deregisterLibrary(ILibrary)
	 */
	public static synchronized void registerLibrary(@Nonnull ILibrary library) {
		if (!libraries.contains(library)) {
			library.install();
			for (final ListIterator<ILibrary> iterator = libraries.listIterator(); iterator.hasNext();) {
				if (iterator.next() == null) {
					iterator.set(library);
					return;
				}
			}
			libraries.add(library);
		}
	}

	/**
	 * Deregister and uninstall a specific library. Normally all registered libraries should be deregistered together using {@link #deregisterLibraries()}
	 * before terminating the program. However, in case a library is not need anymore during runtime, it can be deregistered explicitly with this method.
	 *
	 * @param library the library to deregister.
	 *
	 * @see #deregisterLibraries()
	 */
	public static synchronized void deregisterLibrary(@Nonnull ILibrary library) {
		for (final ListIterator<ILibrary> iterator = libraries.listIterator(); iterator.hasNext();) {
			final ILibrary curLibrary = iterator.next();
			if ((curLibrary != null) && (curLibrary == library)) {
				curLibrary.uninstall();
				iterator.set(null);
				break;
			}
		}
	}

}
