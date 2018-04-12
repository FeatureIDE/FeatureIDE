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
package de.ovgu.featureide.fm.core.io.manager;

import java.nio.file.Path;

import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public interface IFileManager<T> extends IEventManager {

	String getAbsolutePath();

	Path getPath();

	/**
	 * @return A list of problems occurred during last read or write operation.
	 */
	ProblemList getLastProblems();

	/**
	 * Loads the content from the local file and stores it in the local object. To update the persistent and variable object, {@link #override()} must be
	 * called.
	 *
	 * @return {@code true} if successful read, {@code false} otherwise.
	 *
	 * @see #override()
	 */
	boolean read();

	/**
	 * Save last modifications to the local file. Updates (overrides) local object and persistent object.
	 *
	 * @return {@code true} if successful write, {@code false} otherwise.
	 */
	boolean save();

	boolean externalSave(Runnable externalSaveMethod);

	/**
	 * Overrides the variable and persistent object with the local object.
	 */
	void override();

	/**
	 * @return The persistent object.
	 */
	T getObject();

	/**
	 * @return The variable object.
	 */
	T editObject();

	boolean hasChanged();

	IPersistentFormat<T> getFormat();

	void dispose();

}
