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
package de.ovgu.featureide.fm.core.base.impl;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collection;
import java.util.Collections;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureModelLayout;
import de.ovgu.featureide.fm.core.IFMComposerExtension;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelProperty;
import de.ovgu.featureide.fm.core.base.IFeatureModelStructure;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.core.filter.ConcreteFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * The model representation of the feature tree that notifies listeners of
 * changes in the tree.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * 
 */
public class FeatureModel implements IFeatureModel, PropertyConstants {

	protected final FeatureModelAnalyzer analyser = createAnalyser();
	protected final List<IConstraint> constraints = new LinkedList<>();

	/**
	 * A list containing the feature names in their specified order will be
	 * initialized in XmlFeatureModelReader.
	 */
	protected final List<CharSequence> featureOrderList;
	protected boolean featureOrderUserDefined;
	/**
	 * A {@link Map} containing all features.
	 */
	protected final Map<CharSequence, IFeature> featureTable = new ConcurrentHashMap<>();

	protected FMComposerManager fmComposerManager = null;

	protected final List<PropertyChangeListener> listenerList = new LinkedList<>();

	protected final IFeatureModelProperty property;

	protected final RenamingsManager renamingsManager = new RenamingsManager(this);

	protected final IFeatureModelStructure structure;

	protected Object undoContext = null;

	public FeatureModel() {
		featureOrderList = new LinkedList<CharSequence>();
		featureOrderUserDefined = false;

		property = createProperty();
		structure = createStructure();
	}

	protected FeatureModel(FeatureModel oldFeatureModel, IFeature newRoot) {
		featureOrderList = new LinkedList<CharSequence>(oldFeatureModel.featureOrderList);
		featureOrderUserDefined = oldFeatureModel.featureOrderUserDefined;

		property = oldFeatureModel.getProperty().clone(this);
		structure = createStructure();

		if (newRoot == null) {
			structure.setRoot(structure.getRoot().cloneSubtree(this));
			for (final IConstraint constraint : oldFeatureModel.constraints) {
				constraints.add(constraint.clone(this));
			}
		} else {
			structure.setRoot(newRoot.getStructure().cloneSubtree(this));
			for (final IConstraint constraint : oldFeatureModel.constraints) {
				if (featureTable.keySet().containsAll(Functional.mapToStringList(constraint.getContainedFeatures()))) {
					constraints.add(constraint.clone(this));
				}
			}
		}
	}
	
	protected IFeatureModelProperty createProperty() {
		return new FeatureModelProperty(this);
	}
	
	protected IFeatureModelStructure createStructure() {
		return new FeatureModelStructure(this);
	}

	@Override
	public void addConstraint(IConstraint constraint) {
		constraints.add(constraint);
	}

	@Override
	public void addConstraint(IConstraint constraint, int index) {
		constraints.add(index, constraint);
	}

	@Override
	public boolean addFeature(IFeature feature) {
		final CharSequence name = feature.getName();
		if (featureTable.containsKey(name)) {
			return false;
		}
		featureTable.put(name, feature);
		return true;
	}

	@Override
	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	@Override
	public IFeatureModel clone(IFeature newRoot) {
		return new FeatureModel(this, newRoot);
	}

	protected FeatureModelAnalyzer createAnalyser() {
		return new FeatureModelAnalyzer(this);
	}

	@Override
	public void createDefaultValues(CharSequence projectName) {
		String rootName = getValidJavaIdentifier(projectName);
		if (rootName.isEmpty()) {
			rootName = "Root";
		}
		if (featureTable.isEmpty()) {
			final IFeature root = new Feature(this, rootName);
			structure.setRoot(root.getStructure());
			addFeature(root);
		}
		final IFeature feature = new Feature(this, "Base");
		addFeature(feature);

		structure.getRoot().addChild(feature.getStructure());
		structure.getRoot().setAbstract(true);
	}

	@Override
	public boolean deleteFeature(IFeature feature) {
		// the root can not be deleted
		if (feature == structure.getRoot()) {
			return false;
		}

		// check if it exists
		final CharSequence name = feature.getName();
		if (!featureTable.containsKey(name)) {
			return false;
		}

		// use the group type of the feature to delete
		final IFeatureStructure parent = feature.getStructure().getParent();

		if (parent.getChildrenCount() == 1) {
			if (feature.getStructure().isAnd()) {
				parent.setAnd();
			} else if (feature.getStructure().isAlternative()) {
				parent.setAlternative();
			} else {
				parent.setOr();
			}
		}

		// add children to parent
		final int index = parent.getChildIndex(feature.getStructure());
		while (feature.getStructure().hasChildren()) {
			parent.addChildAtPosition(index, feature.getStructure().removeLastChild());
		}

		// delete feature
		parent.removeChild(feature.getStructure());
		featureTable.remove(name);
		featureOrderList.remove(name);
		return true;
	}

	@Override
	public void deleteFeatureFromTable(IFeature feature) {
		featureTable.remove(feature.getName());
	}

	@Override
	public void fireEvent(PropertyChangeEvent event) {
		for (final PropertyChangeListener listener : listenerList) {
			listener.propertyChange(event);
		}
	}

	protected void fireEvent(final String action) {
		fireEvent(new PropertyChangeEvent(this, action, Boolean.FALSE, Boolean.TRUE));
	}

	@Override
	public FeatureModelAnalyzer getAnalyser() {
		return analyser;
	}

	@Override
	public int getConstraintCount() {
		return constraints.size();
	}

	@Override
	public int getConstraintIndex(IConstraint constraint) {
		return constraints.indexOf(constraint);
	}

	@Override
	public List<IConstraint> getConstraints() {
		return Collections.unmodifiableList(constraints);
	}

	@Override
	public IFeature getFeature(String name) {
		return featureTable.get(name);
	}

	@Override
	public Collection<CharSequence> getFeatureOrderList() {
		if (featureOrderList.isEmpty()) {
			return Functional.mapToStringList(Functional.filter(getFeatures(), new ConcreteFeatureFilter()));
		}
		return featureOrderList;
	}

	@Override
	public Collection<IFeature> getFeatures() {
		return Collections.unmodifiableCollection(featureTable.values());
	}

	@Override
	public IFMComposerExtension getFMComposerExtension() {
		return getFMComposerManager(null).getFMComposerExtension();
	}

	@Override
	public FMComposerManager getFMComposerManager(IProject project) {
		if (fmComposerManager == null) {
			fmComposerManager = new FMComposerManager(project);
		}
		return fmComposerManager;
	}

	@Override
	public int getNumberOfFeatures() {
		return featureTable.size();
	}

	@Override
	public IFeatureModelProperty getProperty() {
		return property;
	}

	@Override
	public RenamingsManager getRenamingsManager() {
		return renamingsManager;
	}

	@Override
	public IFeatureModelStructure getStructure() {
		return structure;
	}

	public Object getUndoContext() {
		return undoContext;
	}

	/**
	 * Removes all invalid java identifiers form a given string.
	 */
	protected String getValidJavaIdentifier(CharSequence s) {
		final StringBuilder stringBuilder = new StringBuilder();
		int i = 0;
		for (; i < s.length(); i++) {
			if (Character.isJavaIdentifierStart(s.charAt(i))) {
				stringBuilder.append(s.charAt(i));
				i++;
				break;
			}
		}
		for (; i < s.length(); i++) {
			if (Character.isJavaIdentifierPart(s.charAt(i))) {
				stringBuilder.append(s.charAt(i));
			}
		}
		return stringBuilder.toString();
	}

	@Override
	public void handleModelDataChanged() {
		fireEvent(MODEL_DATA_CHANGED);
	}

	@Override
	public void handleModelDataLoaded() {
		fireEvent(MODEL_DATA_LOADED);

	}

	@Override
	public IFMComposerExtension initFMComposerExtension(IProject project) {
		return getFMComposerManager(project);
	}

	@Override
	public boolean isFeatureOrderUserDefined() {
		return featureOrderUserDefined;
	}

	@Override
	public void removeConstraint(IConstraint constraint) {
		constraints.remove(constraint);
	}

	@Override
	public void removeConstraint(int index) {
		constraints.remove(index);

	}

	@Override
	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	@Override
	public void replaceConstraint(IConstraint constraint, int index) {
		constraints.set(index, constraint);
	}

	@Override
	public void reset() {
		structure.setRoot(null);

		featureTable.clear();
		renamingsManager.clear();
		constraints.clear();
		featureOrderList.clear();

		property.reset();
	}

	@Override
	public void setConstraints(Iterable<IConstraint> constraints) {
		this.constraints.clear();
		this.constraints.addAll(Functional.toList(constraints));
	}

	@Override
	public void setFeatureOrderList(List<String> featureOrderList) {
		this.featureOrderList.clear();
		this.featureOrderList.addAll(featureOrderList);
	}

	@Override
	public void setFeatureOrderUserDefined(boolean featureOrderUserDefined) {
		this.featureOrderUserDefined = featureOrderUserDefined;
	}

	@Override
	public void setFeatureTable(Hashtable<CharSequence, IFeature> featureTable) {
		this.featureTable.clear();
		this.featureTable.putAll(featureTable);
	}

	public void setUndoContext(Object undoContext) {
		this.undoContext = undoContext;
	}

	@Override
	public IGraphicalFeatureModel getGraphicRepresenation() {
		throw new UnsupportedOperationException ("Not implemented yet");
	}

	@Override
	public Map<CharSequence, IFeature> getFeatureTable() {
		return featureTable;
	}

	@Override
	public IFeatureModel clone(IFeature oldFeatureModel, boolean complete) {
		throw new UnsupportedOperationException ("Not implemented yet");
	}

	@Override
	public FeatureModelLayout getLayout() {
		throw new UnsupportedOperationException ("Not implemented yet");
	}

}
