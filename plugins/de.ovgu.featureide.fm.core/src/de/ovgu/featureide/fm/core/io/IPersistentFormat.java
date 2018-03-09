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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io;

import de.ovgu.featureide.fm.core.IExtension;

/**
 * Interface for saving and loading data.
 *
 * @author Sebastian Krieter
 */
public interface IPersistentFormat<T> extends IExtension {

	ProblemList read(T object, CharSequence source);

	String write(T object);

	String getSuffix();

	String getName();

	IPersistentFormat<T> getInstance();

	boolean supportsRead();

	boolean supportsWrite();

	boolean supportsContent(CharSequence content);

	boolean supportsContent(LazyReader reader);

}
