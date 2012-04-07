/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io;

import java.io.File;

import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.FeatureModel;


/**
 * Writes a feature model to a file or string.
 * 
 * @author Thomas Thuem
 */
public interface IFeatureModelWriter {

	/**
	 * Returns the feature model to write out.
	 * 
	 * @return the model to write
	 */
	public FeatureModel getFeatureModel();
	
	/**
	 * Sets the feature model to be saved in a textual representation.
	 * 
	 * @param featureModel the model to write
	 */
	public void setFeatureModel(FeatureModel featureModel);

	/**
	 * Saves a feature model to a file.
	 * 
	 * @param file
	 * @throws CoreException
	 */
//	public abstract void writeToFile(IFile file) throws CoreException;
	
	/**
	 * Saves a feature model to a file.
	 * 
	 * @param file
	 * @throws CoreException
	 */
	public abstract void writeToFile(File file);
	
	/**
	 * Converts a feature model to a textual representation.
	 * 
	 * @return
	 */
	public abstract String writeToString();

}
