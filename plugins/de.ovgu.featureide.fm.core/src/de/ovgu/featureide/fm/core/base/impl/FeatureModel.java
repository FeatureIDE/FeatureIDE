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
import java.io.File;
import java.util.Collection;
import java.util.Collections;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.eclipse.core.resources.IProject;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureModelLayout;
import de.ovgu.featureide.fm.core.IFMComposerExtension;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelLayout;
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
 * @author Marcus Pinnecke
 * 
 */
public class FeatureModel implements IFeatureModel, PropertyConstants {
	
	private static long NEXT_ID = 0;
	
	protected static final synchronized long getNextId() {
		return NEXT_ID++;
	}

	private long id;

	private long nextElementId = 0;
	
	public final synchronized long getNextElementId() {
		return nextElementId++;
	}

	protected final FeatureModelAnalyzer analyser;
	protected final List<IConstraint> constraints = new LinkedList<>();
	
	/**
	 * A list containing the feature names in their specified order will be
	 * initialized in XmlFeatureModelReader.
	 */
	protected final List<String> featureOrderList;
	protected boolean featureOrderUserDefined;
	/**
	 * A {@link Map} containing all features.
	 */
	protected final Map<String, IFeature> featureTable = new ConcurrentHashMap<>();

	protected FMComposerManager fmComposerManager = null;

	protected final List<PropertyChangeListener> listenerList = new LinkedList<>();

	protected final IFeatureModelProperty property;

	protected final RenamingsManager renamingsManager = new RenamingsManager(this);

	protected final IFeatureModelStructure structure;

	protected final IGraphicalFeatureModel graphicalFeatureModel;

	protected final IFeatureModelLayout modelLayout;

	protected Object undoContext = null;
	private File sourceFile;

	public FeatureModel() {
		id = getNextId();
		featureOrderList = new LinkedList<String>();
		featureOrderUserDefined = false;

		property = createProperty();
		structure = createStructure();
		graphicalFeatureModel = createGraphicalFeatureModel();
		modelLayout = createFeatureModelLayout();
		
		analyser = createAnalyser();
	}

	protected FeatureModel(FeatureModel oldFeatureModel, IFeature newRoot) {
		id = oldFeatureModel.getId();
		featureOrderList = new LinkedList<String>(oldFeatureModel.featureOrderList);
		featureOrderUserDefined = oldFeatureModel.featureOrderUserDefined;

		property = oldFeatureModel.getProperty().clone(this);
		structure = createStructure();
		graphicalFeatureModel = oldFeatureModel.getGraphicRepresenation(); // TODO: Marcus XXX clone here?
		modelLayout = oldFeatureModel.getLayout();

		this.sourceFile = oldFeatureModel.sourceFile;

		if (newRoot == null) {
			structure.setRoot(oldFeatureModel.getStructure().getRoot().cloneSubtree(this));// structure.getRoot().cloneSubtree(this));
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
		analyser = createAnalyser();
	}

	protected IFeatureModelProperty createProperty() {
		return new FeatureModelProperty(this);
	}

	protected IFeatureModelStructure createStructure() {
		return new FeatureModelStructure(this);
	}

	protected IGraphicalFeatureModel createGraphicalFeatureModel() {
		return GraphicMap.getInstance().getGraphicRepresentation(this);
	}

	private IFeatureModelLayout createFeatureModelLayout() {
		return new FeatureModelLayout();
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
		featureTable.put(name.toString(), feature);
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
		if (feature.equals(structure.getRoot().getFeature())) {
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
	public IFeature getFeature(CharSequence name) {
		return featureTable.get(name);
	}

	@Override
	public Collection<String> getFeatureOrderList() {
		if (featureOrderList.isEmpty()) {
			return Functional.toList(Functional.mapToStringList(Functional.filter(getFeatures(), new ConcreteFeatureFilter())));
		}
		return Collections.unmodifiableCollection(featureOrderList);
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
		for (CharSequence cs : featureOrderList)
			this.featureOrderList.add(cs.toString());
	}

	@Override
	public void setFeatureOrderUserDefined(boolean featureOrderUserDefined) {
		this.featureOrderUserDefined = featureOrderUserDefined;
	}

	@Override
	public void setFeatureTable(Hashtable<String, IFeature> featureTable) {
		this.featureTable.clear();
		this.featureTable.putAll(featureTable);
	}

	public void setUndoContext(Object undoContext) {
		this.undoContext = undoContext;
	}

	@Override
	public IGraphicalFeatureModel getGraphicRepresenation() {
		return graphicalFeatureModel;
	}

	@Override
	public Map<String, IFeature> getFeatureTable() {
		return featureTable;
	}

	@Override
	public IFeatureModelLayout getLayout() {
		return modelLayout;
	}

	@Override
	public IFeatureModel clone(IFeatureModel oldFeatureModel, boolean complete) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public IFeatureModel clone() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public IFeatureModel deepClone() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public IFeatureModel deepClone(boolean complete) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public Object getUndoContext(Object undoContext) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public boolean isFeatureOrderInXML() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public Object setFeatureOrderInXML(IFeatureModel featureModel, boolean featureOrderInXML) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public void refreshContextMenu() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public void setFeatureOrderListItem(int i, String newName) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public String toString() {
		// ! DO NOT CHANGE THIS !
		// The method call is required for hashCode and equals and might damage some
		// behavior if after a changes two not identical models are represented with
		// the same string
		StringBuilder sb = new StringBuilder("FeatureModel(");
		if (getStructure().getRoot() != null) {
			sb.append("Structure=[");
			FeatureUtils.print(getStructure().getRoot().getFeature(), sb);
			sb.append("], Constraints=[");
			print(getConstraints(), sb);
			sb.append("], ");
		} else {
			sb.append("Feature model without root feature.");
		}
		StringBuilder features = new StringBuilder();
		String[] feat = featureTable.keySet().toArray(new String[featureTable.keySet().size()]);
		for (int i = 0; i < feat.length; i++) {
			features.append(feat[i]);
			if (i + 1 < feat.length)
				features.append(", ");
		}
		sb.append("Features=[" + (features.length() > 0 ? features.toString() : ""));
		sb.append("])");
		return sb.toString();
	}

	private void print(List<IConstraint> constraints, StringBuilder sb) {
		for (int i = 0; i < constraints.size(); i++) {
			sb.append("[");
			sb.append(NodeWriter.nodeToString(constraints.get(i).getNode()));
			sb.append("]");
			if (i + 1 < constraints.size())
				sb.append(", ");
		}
	}

	@Override
	public void setSourceFile(File file) {
		this.sourceFile = file;
		if (file != null) {
			id = ModelFileIdMap.getModelId(this, file);
		}
	}

	@Override
	public File getSourceFile() {
		return this.sourceFile;
	}

//	@Override
//	public int hashCode() {
//		return toString().hashCode();
//	}
//
//	@Override
//	public boolean equals(Object obj) {
//		if (this == obj)
//			return true;
//		if (obj == null || getClass() != obj.getClass())
//			return false;
//		FeatureModel other = (FeatureModel) obj;
//		if (structure == null) {
//			if (other.structure != null) {
//				return false;
//			}
//		} else
//			return this.toString().equals(obj.toString());
//		return false;
//	}

	@Override
	public long getId() {
		return id;
	}
	
	@Override
	public int hashCode() {
		return (int) (37 * id);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		FeatureModel other = (FeatureModel) obj;
		return id == other.id;
	}

}
