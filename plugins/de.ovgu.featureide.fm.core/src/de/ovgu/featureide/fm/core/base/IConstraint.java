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

import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.ConstraintAttribute;

/**
 * Interface for a class that represents a constraint.</br>
 * Can be instantiated via {@link IFeatureModelFactory}.
 * 
 * @author Sebastian Krieter
 */
public interface IConstraint {

	void addListener(PropertyChangeListener listener);

	IConstraint clone(IFeatureModel newFeatureModel);

	void fireEvent(PropertyChangeEvent event);

	ConstraintAttribute getConstraintAttribute();

	Collection<IFeature> getContainedFeatures();

	Collection<IFeature> getDeadFeatures();

	Collection<IFeature> getDeadFeatures(SatSolver solver, IFeatureModel fm, Collection<IFeature> fmDeadFeatures);

	Collection<IFeature> getFalseOptional();

	IFeatureModel getFeatureModel();

	Node getNode();

	boolean hasHiddenFeatures();

	void removeListener(PropertyChangeListener listener);

	void setConstraintAttribute(ConstraintAttribute attri, boolean fire);

	void setContainedFeatures();

	void setDeadFeatures(Collection<IFeature> deadFeatures);

	boolean setFalseOptionalFeatures(IFeatureModel clone, Collection<IFeature> fmFalseOptionals);

}
