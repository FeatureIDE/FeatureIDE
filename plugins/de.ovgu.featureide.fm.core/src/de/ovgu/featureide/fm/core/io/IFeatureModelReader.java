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
import java.io.FileNotFoundException;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Parses a feature model from a given file or string.
 *
 * @deprecated Use {@link IFeatureModelFormat} and {@link FileHandler} instead.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public interface IFeatureModelReader {

	/**
	 * Returns the feature model where the read data is stored.
	 *
	 * @return the model to fill
	 */
	public IFeatureModel getFeatureModel();

	/**
	 * Sets the feature model where the read data is stored.
	 *
	 * @param featureModel the model to fill
	 */
	public void setFeatureModel(IFeatureModel featureModel);

	/**
	 * Parses a specific feature model file.
	 *
	 * @param file the feature model file
	 * @throws UnsupportedModelException
	 * @throws FileNotFoundException
	 */
//	public void readFromFile(IFile file)
//			throws UnsupportedModelException, FileNotFoundException;
	/**
	 * Parses a specific feature model file.
	 *
	 * @param file the feature model file
	 * @throws UnsupportedModelException
	 * @throws FileNotFoundException
	 */
	public void readFromFile(File file) throws UnsupportedModelException, FileNotFoundException;

	/**
	 * Parses a textual representation of a feature model.
	 *
	 * @param text
	 * @throws UnsupportedModelException
	 */
	public void readFromString(String text) throws UnsupportedModelException;

	/**
	 * Returns warnings occurred while last parsing.
	 *
	 * @return
	 */
	public List<Problem> getWarnings();

	/**
	 * Set the source file of the textual representation of the feature model.
	 *
	 * @param featureModelFile the source file
	 */
	public void setFile(File featureModelFile);

}
