/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collection;

/**
 * Interface for a class that represents a feature.</br>
 * Can be instantiated via {@link IFeatureModelFactory}.
 * 
 * @author Sebastian Krieter
 */
public interface IFeature extends PropertyChangeListener {

	void addListener(PropertyChangeListener listener);

	IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure);

	void fireEvent(PropertyChangeEvent event);

	IFeatureModel getFeatureModel();

	IFeatureProperty getProperty();

	IFeatureStructure getStructure();

	int getId();

	String getName();

	void removeListener(PropertyChangeListener listener);

	void setName(String name);
	
	Collection<IGraphicalFeature> getGraphicRepresenation(); // Added, Marcus Pinnecke 31.08.15

}
