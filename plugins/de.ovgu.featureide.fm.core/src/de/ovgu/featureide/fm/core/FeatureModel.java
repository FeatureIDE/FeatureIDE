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
package de.ovgu.featureide.fm.core;

import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY_FEATURE_MODEL;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collection;
import java.util.Collections;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import org.eclipse.core.resources.IProject;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.DeprecatedFeatureModel;
import de.ovgu.featureide.fm.core.EmptyColorschemeTable;
import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureModelLayout;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.IFMComposerExtension;
import de.ovgu.featureide.fm.core.IGraphicItem;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.IGraphicItem.GraphicItem;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
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
public class FeatureModel extends DeprecatedFeatureModel implements PropertyConstants, IGraphicItem {
	
	public IFeatureModel model;
	
	public FeatureModel() {
		throw IllegalAccessException("Do not use this construction any longer. Use direct assigment to member 'model' instead");
	}

	protected FeatureModel(FeatureModel oldFeatureModel, boolean complete) {
		throw IllegalAccessException("Do not use this construction any longer. Use direct assigment to member 'model' instead");	
	}

	protected FeatureModel(FeatureModel oldFeatureModel, boolean complete) {
		this.model = oldFeatureModel.model.clone(oldFeatureModel, complete);
	}
	
	protected FeatureModelAnalyzer createAnalyser() {
		return model.getAnalyser();
	}
	
	@Override
    public FeatureModelAnalyzer getAnalyser() {
		return model.getAnalyser();
    }

	@Override
    public FeatureModelLayout getLayout() {
		return model.getLayout();
    }

	public ColorschemeTable getColorschemeTable() {
		return model.getGraphicRepresenation().getColorschemeTable();
	}
	
	@Override
	public FMComposerManager getFMComposerManager(final IProject project) {
		return model.getFMComposerManager(project);
	}

	public IFMComposerExtension initFMComposerExtension(final IProject project) {
		return model.initFMComposerExtension(project);
	}

	public IFMComposerExtension getFMComposerExtension() {
		return model.getFMComposerExtension();
	}
	
	@Override
	public RenamingsManager getRenamingsManager() {
		return model.getRenamingsManager();
	}
	
	public void reset() {
		return model.reset();
	}
	
	public void createDefaultValues(String projectName) {
		return model.createDefaultValues(projectName);
	}
	
	public void setRoot(IFeature root) {
		model.getStructure().setRoot(root);
	}
	
	public IFeature getRoot() {
		return model.getStructure().getRoot();
	}

	public void setFeatureTable(final Hashtable<String, IFeature> featureTable) {
		model.setFeatureTable(featureTable);
	}
	
	public boolean addFeature(IFeature feature) {
		model.addFeature(feature);
	}
	
	public Collection<IFeature> getFeatures() {
		return model.getFeatures();
	}
	
	@CheckForNull
	public IFeature getFeature(String name) {
		return model.getFeature(name);
	}

	@Nonnull
	public Collection<IFeature> getConcreteFeatures() {
		return Functional.toList(FeatureUtils.extractConcreteFeatures(model));
	}
	
	@Nonnull
	public List<String> getConcreteFeatureNames() {
		return FeatureUtils.extractConcreteFeaturesAsStringList(model);
	}
	
	public Collection<IFeature> getFeaturesPreorder() {
		return model.getStructure().getFeaturesPreorder();
	}

	public List<String> getFeatureNamesPreorder() {
		return Functional.toList(FeatureUtils.extractFeatureNames(model.getStructure().getFeaturesPreorder()));
	}
	
	@Deprecated
	public boolean isConcrete(String featureName) {
		for (IFeature feature : FeatureUtils.extractConcreteFeatures(model))
			if (feature.getName().equals(featureName))
				return true;
		return false;
	}
	
	protected Map<String, IFeature> getFeatureTable() {
		return model.getFeatureTable();
	}
	
	public Set<String> getFeatureNames() {
		return Functional.toSet(FeatureUtils.extractFeatureNames(model.getFeatures()));
	}
	
	public int getNumberOfFeatures() {
		return model.getNumberOfFeatures();
	}

	public void deleteFeatureFromTable(IFeature feature) {
		model.deleteFeatureFromTable(feature);
	}

	public boolean deleteFeature(IFeature feature) {
		return model.deleteFeature(feature);
	}
	
	public void replaceRoot(IFeature feature) {
		model.getStructure().replaceRoot(feature);
	}

	public void setConstraints(final LinkedList<IConstraint> constraints) {
		model.setConstraints(constraints);
	}
	
	public void addPropositionalNode(Node node) {
		model.getConstraints().add(new Constraint(node));
	}
	
	public void addConstraint(IConstraint constraint) {
		model.getConstraints().add(constraint);
	}

	public void addPropositionalNode(Node node, int index) {
		model.getConstraints().add(index, new Constraint(node));
	}
	
	public void addConstraint(IConstraint constraint, int index) {
		model.getConstraints().add(index, constraint);
	}
	
	public List<Node> getPropositionalNodes() {
		return Functional.toList(FeatureUtils.getPropositionalNodes(model.getConstraints()));
	}
	
	public Node getConstraint(int index) {
		return FeatureUtils;
	}
	                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
	public List<IConstraint> getConstraints() {
	
	}

	public int getConstraintIndex(IConstraint constraint) {
	
	}

	public void removePropositionalNode(Node node) {
	
	}

	public void removeConstraint(IConstraint constraint) {
	
	}

	public void removeConstraint(int index) {
	
	}
	
	public void replacePropNode(int index, Node node) {
	
	}
	
	public int getConstraintCount() {
	
	}
	
	public List<String> getAnnotations() {
	
	}

	public void addAnnotation(String annotation) {
	
	}

	public List<String> getComments() {
	
	}

	public void addComment(String comment) {
	
	}
	
	public void addListener(PropertyChangeListener listener) {
	
	}

	public void removeListener(PropertyChangeListener listener) {
	
	}
	
	public void handleModelDataLoaded() {
	
	}

	public void handleModelDataChanged() {
	
	}
	
	public void handleModelLayoutChanged() {
	
	}
	
	public void handleLegendLayoutChanged() {
	
	}
	
	public void refreshContextMenu() {
	
	}
	
	public void redrawDiagram() {
	
	}
	
	@Override
	public FeatureModel clone() {
	
	}
	
	public FeatureModel deepClone() {
	
	}
	
	public FeatureModel deepClone(boolean complete) {
	
	}

	public boolean hasMandatoryFeatures() {
	
	}

	public boolean hasOptionalFeatures() {
	
	}

	public boolean hasAndGroup() {
	
	}

	public boolean hasAlternativeGroup() {
		
	}
	
	public boolean hasOrGroup() {
	
	}

	public boolean hasAbstract() {
	
	}

	public boolean hasConcrete() {
	
	}
	
	public int numOrGroup() {
	
	}
	
	public int numAlternativeGroup() {
	
	}
	
	public boolean hasHidden() {
	
	}

	public boolean hasIndetHidden() {
	
	}
	
	public boolean hasUnsatisfiableConst() {
	
	}
	
	public boolean hasTautologyConst() {
	
	}
	
	public boolean hasDeadConst() {
	
	}
	
	public boolean hasVoidModelConst() {
	
	}
	
	public boolean hasRedundantConst() {
	
	}

	public boolean hasFalseOptionalFeatures() {
	
	}

	public void setUndoContext(Object undoContext) {
	
	}

	public Object getUndoContext() {
	
	}

	public List<String> getFeatureOrderList() {
	
	}

	public void setFeatureOrderList(final List<String> featureOrderList) {
	
	}

	public boolean isFeatureOrderUserDefined() {
	
	}

	public void setFeatureOrderUserDefined(boolean featureOrderUserDefined) {
	
	}

	public boolean isFeatureOrderInXML() {
	
	}

	public void setFeatureOrderInXML(boolean featureOrderInXML) {
	
	}
	
	@Override
	public String toString() {
	
	}
	
	@Override
	public boolean equals(Object obj) {
	
	}
	
	@Override
	public int hashCode() {
	
	}

	@Override
	public GraphicItem getItemType() {
	
	}

}
