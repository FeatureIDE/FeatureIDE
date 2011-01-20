/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.fstmodel;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;

public interface IFSTModel extends IFSTModelElement {

	/**
	 * Returns the number of features, that were used to build the current
	 * version of the FeatureIDE project according to the current configuration file
	 * 
	 * @return Number of selected features
	 */
	public int getNumberOfSelectedFeatures();

	/**
	 * Returns all selected features ordered by the order in the configuration file
	 * 
	 * @return Selected features
	 */
	public ArrayList<IFeature> getSelectedFeatures();

	/**
	 * Returns the total number of features of the FeatureIDE project
	 * 
	 * @return Number of available features
	 */
	public int getNumberOfFeatures();

	/**
	 * Returns all available features of the FeatureIDE project
	 * 
	 * @return Array of available features
	 */
	public IFeature[] getFeatures();

	/**
	 * Returns the feature object for the given feature name
	 * 
	 * @param featureName
	 *            The name of the feature
	 * @return The feature object
	 */
	public IFeature getFeature(String featureName);

	/**
	 * Returns the number of classes according to the currently selected
	 * features
	 * 
	 * @return Number of classes
	 */
	public int getNumberOfClasses();

	/**
	 * Returns all classes according to the currently selected features
	 * 
	 * @return Array of classes
	 */
	public IClass[] getClasses();

	/**
	 * Returns the class for the given file
	 * 
	 * @param file
	 *            A file
	 * @return the class for the given file
	 */
	public IClass getClass(IFile file);

	/**
	 * called when this model is obsolete and replaced by a new model
	 */
	public void markObsolete();

}
