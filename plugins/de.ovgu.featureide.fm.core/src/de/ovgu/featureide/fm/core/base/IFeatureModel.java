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
import java.io.File;
import java.util.Collection;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.IFMComposerExtension;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.base.impl.Constraint;

/**
 * Interface for a class that represents a feature model.</br>
 * Can be instantiated via {@link IFeatureModelFactory}.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public interface IFeatureModel extends Cloneable {
	
	long getId();

	void addConstraint(IConstraint constraint);

	void addConstraint(IConstraint constraint, int index);

	boolean addFeature(IFeature feature);

	void addListener(PropertyChangeListener listener);

	IFeatureModel clone(IFeature newRoot);

	IFeatureModel clone(IFeatureModel oldFeatureModel, boolean complete);

	void createDefaultValues(CharSequence projectName);

	boolean deleteFeature(IFeature feature);

	void deleteFeatureFromTable(IFeature feature);

	void fireEvent(PropertyChangeEvent event);

	FeatureModelAnalyzer getAnalyser();

	int getConstraintCount();

	int getConstraintIndex(IConstraint constraint);

	List<IConstraint> getConstraints();

	IFeature getFeature(CharSequence name);

	Collection<String> getFeatureOrderList();

	Iterable<IFeature> getFeatures();

	IFMComposerExtension getFMComposerExtension();

	FMComposerManager getFMComposerManager(final IProject project);

	int getNumberOfFeatures();

	IFeatureModelProperty getProperty();

	RenamingsManager getRenamingsManager();

	IFeatureModelStructure getStructure();

	void handleModelDataChanged();

	void handleModelDataLoaded();

	IFMComposerExtension initFMComposerExtension(final IProject project);

	boolean isFeatureOrderUserDefined();

	void removeConstraint(IConstraint constraint);

	void removeConstraint(int index);

	void removeListener(PropertyChangeListener listener);

	void replaceConstraint(IConstraint constraint, int index);

	void reset();

	void setConstraints(final Iterable<IConstraint> constraints);

	void setFeatureOrderList(final List<String> featureOrderList);

	void setFeatureOrderUserDefined(boolean featureOrderUserDefined);

	void setFeatureTable(final Hashtable<String, IFeature> featureTable);

	IGraphicalFeatureModel getGraphicRepresenation(); // Added, Marcus Pinnecke 31.08.15

	Map<String, IFeature> getFeatureTable(); // Added, Marcus Pinnecke 31.08.15

	IFeatureModelLayout getLayout(); // Added, Marcus Pinnecke 13.09.15

	IFeatureModel clone();

	IFeatureModel deepClone();

	IFeatureModel deepClone(boolean complete);

	Object getUndoContext(Object undoContext);

	Object getUndoContext();

	boolean isFeatureOrderInXML();

	Object setFeatureOrderInXML(IFeatureModel featureModel, boolean featureOrderInXML);

	void refreshContextMenu();

	void setUndoContext(Object undoContext);

	void setFeatureOrderListItem(int i, String newName);

	void setSourceFile(File file);

	File getSourceFile();

	long getNextElementId();

	void setConstraint(int index, Constraint constraint);

}
