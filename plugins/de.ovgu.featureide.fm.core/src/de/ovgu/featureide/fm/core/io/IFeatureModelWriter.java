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
package de.ovgu.featureide.fm.core.io;

import java.io.File;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Writes a feature model to a file or string.
 *
 * @deprecated Use {@link IFeatureModelFormat} and {@link FileHandler} instead.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public interface IFeatureModelWriter {

	/**
	 * Returns the feature model to write out.
	 *
	 * @return the model to write
	 */
	public IFeatureModel getFeatureModel();

	/**
	 * Sets the feature model to be saved in a textual representation.
	 *
	 * @param featureModel the model to write
	 */
	public void setFeatureModel(IFeatureModel featureModel);

	/**
	 * Saves a feature model to a file.
	 *
	 * @param file
	 * @throws org.eclipse.core.runtime.CoreException
	 */
	public abstract void writeToFile(File file);

	/**
	 * Converts a feature model to a textual representation.
	 *
	 * @return
	 */
	public abstract String writeToString();

}
