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

import java.beans.PropertyChangeListener;
import java.util.Collection;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import org.eclipse.core.resources.IProject;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;
import static de.ovgu.featureide.fm.core.base.FeatureUtils.*;

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
		throw new RuntimeException("Do not use this construction any longer. Use direct assigment to member 'model' instead");
	}

	public FeatureModel(IFeatureModel model) {
		this.model = model;
	}

	protected FeatureModel(FeatureModel oldFeatureModel, boolean complete) {
		this.model = oldFeatureModel.model.clone(oldFeatureModel.model, complete);
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
		FeatureUtils.reset(model);
	}

	public void createDefaultValues(String projectName) {
		FeatureUtils.createDefaultValues(model, projectName);
	}

	public void setRoot(Feature root) {
		FeatureUtils.setRoot(model, convert(root));
	}

	public Feature getRoot() {
		return convert(FeatureUtils.getRoot(model));
	}

	public void setFeatureTable(final Hashtable<String, Feature> featureTable) {
		Hashtable<String, IFeature> iFeatureTable = new Hashtable<>();
		for (String key : Functional.toIterator(featureTable.keys()))
			iFeatureTable.put(key, convert(featureTable.get(key)));
		FeatureUtils.setFeatureTable(model, iFeatureTable);
	}

	public boolean addFeature(Feature feature) {
		return FeatureUtils.addFeature(model, convert(feature));
	}

	public Collection<Feature> getFeatures() {
		return Functional.retype(FeatureUtils.getFeatures(model), FeatureUtils.IFEATURE_TO_FEATURE);
	}

	@CheckForNull
	public Feature getFeature(String name) {
		return convert(FeatureUtils.getFeature(model, name));
	}

	@Nonnull
	public Collection<Feature> getConcreteFeatures() {
		return Functional.retype(FeatureUtils.getConcreteFeatures(model), FeatureUtils.IFEATURE_TO_FEATURE);
	}

	@Nonnull
	public List<String> getConcreteFeatureNames() {
		return Functional.toList(FeatureUtils.getConcreteFeatureNames(model));
	}

	public Collection<Feature> getFeaturesPreorder() {
		return Functional.retype(FeatureUtils.getFeaturesPreorder(model), FeatureUtils.IFEATURE_TO_FEATURE);
	}

	public List<String> getFeatureNamesPreorder() {
		return FeatureUtils.getFeatureNamesPreorder(model);
	}

	@Deprecated
	public boolean isConcrete(String featureName) {
		return FeatureUtils.isConcrete(model, featureName);
	}

	protected Map<String, Feature> getFeatureTable() {
		Map<String, Feature> result = new HashMap<>();
		final Map<String, IFeature> map = FeatureUtils.getFeatureTable(model);
		for (String key : map.keySet())
			result.put (key, convert(map.get(key)));				
		return result;
	}

	public Set<String> getFeatureNames() {
		return FeatureUtils.getFeatureNames(model);
	}

	public int getNumberOfFeatures() {
		return FeatureUtils.getNumberOfFeatures(model);
	}

	public void deleteFeatureFromTable(Feature feature) {
		FeatureUtils.deleteFeatureFromTable(model, convert(feature));
	}

	public boolean deleteFeature(Feature feature) {
		return FeatureUtils.deleteFeature(model, convert(feature));
	}

	public void replaceRoot(Feature feature) {
		FeatureUtils.replaceRoot(model, convert(feature));
	}

	public void setConstraints(final LinkedList<Constraint> constraints) {
		FeatureUtils.setConstraints(model, Functional.retype(constraints, FeatureUtils.CONSTRAINT_TO_ICONSTRANT);
	}

	public void addPropositionalNode(Node node) {
		FeatureUtils.addPropositionalNode(model, node);
	}

	public void addConstraint(Constraint constraint) {
		FeatureUtils.addConstraint(model, constraint);
	}

	public void addPropositionalNode(Node node, int index) {
		FeatureUtils.addPropositionalNode(model, node, index);
	}

	public void addConstraint(Constraint constraint, int index) {
		FeatureUtils.addConstraint(model, constraint, index);
	}

	public List<Node> getPropositionalNodes() {
		return Functional.toList(FeatureUtils.getPropositionalNodes(model));
	}

	public Node getConstraint(int index) {
		return FeatureUtils.getConstraint(model, index);
	}

	public List<Constraint> getConstraints() {
		return FeatureUtils.getConstraints(model);
	}

	public int getConstraintIndex(Constraint constraint) {
		return FeatureUtils.getConstraintIndex(model, constraint);
	}

	public void removePropositionalNode(Node node) {
		FeatureUtils.removePropositionalNode(model, node);
	}

	public void removeConstraint(Constraint constraint) {
		FeatureUtils.removeConstraint(model, constraint);
	}

	public void removeConstraint(int index) {
		FeatureUtils.removeConstraint(model, index);
	}

	public void replacePropNode(int index, Node node) {
		FeatureUtils.replacePropNode(model, index, node);
	}

	public int getConstraintCount() {
		return FeatureUtils.getConstraintCount(model);
	}

	public List<String> getAnnotations() {
		return FeatureUtils.getAnnotations(model);
	}

	public void addAnnotation(String annotation) {
		FeatureUtils.addAnnotation(model, annotation);
	}

	public List<String> getComments() {
		return FeatureUtils.getComments(model);
	}

	public void addComment(String comment) {
		FeatureUtils.addComment(model, comment);
	}

	public void addListener(PropertyChangeListener listener) {
		FeatureUtils.addListener(model, listener);
	}

	public void removeListener(PropertyChangeListener listener) {
		FeatureUtils.removeListener(model, listener);
	}

	public void handleModelDataLoaded() {
		FeatureUtils.handleModelDataLoaded(model);
	}

	public void handleModelDataChanged() {
		FeatureUtils.handleModelDataChanged(model);
	}

	public void handleModelLayoutChanged() {
		FeatureUtils.handleModelLayoutChanged(model);
	}

	public void handleLegendLayoutChanged() {
		FeatureUtils.handleLegendLayoutChanged(model);
	}

	public void refreshContextMenu() {
		FeatureUtils.refreshContextMenu(model);
	}

	public void redrawDiagram() {
		FeatureUtils.redrawDiagram(model);
	}

	@Override
	public FeatureModel clone() {
		return new FeatureModel(FeatureUtils.clone(model));
	}

	public FeatureModel deepClone() {
		return new FeatureModel(FeatureUtils.deepClone(model));
	}

	public FeatureModel deepClone(boolean complete) {
		return new FeatureModel(FeatureUtils.deepClone(model, complete));
	}

	public boolean hasMandatoryFeatures() {
		return FeatureUtils.hasMandatoryFeatures(model);
	}

	public boolean hasOptionalFeatures() {
		return FeatureUtils.hasOptionalFeatures(model);
	}

	public boolean hasAndGroup() {
		return FeatureUtils.hasAndGroup(model);
	}

	public boolean hasAlternativeGroup() {
		return FeatureUtils.hasAlternativeGroup(model);
	}

	public boolean hasOrGroup() {
		return FeatureUtils.hasOrGroup(model);
	}

	public boolean hasAbstract() {
		return FeatureUtils.hasAbstract(model);
	}

	public boolean hasConcrete() {
		return FeatureUtils.hasConcrete(model);
	}

	public int numOrGroup() {
		return FeatureUtils.numOrGroup(model);
	}

	public int numAlternativeGroup() {
		return FeatureUtils.numAlternativeGroup(model);
	}

	public boolean hasHidden() {
		return FeatureUtils.hasHidden(model);
	}

	public boolean hasIndetHidden() {
		return FeatureUtils.hasIndetHidden(model);
	}

	public boolean hasUnsatisfiableConst() {
		return FeatureUtils.hasUnsatisfiableConst(model);
	}

	public boolean hasTautologyConst() {
		return FeatureUtils.hasTautologyConst(model);
	}

	public boolean hasDeadConst() {
		return FeatureUtils.hasDeadConst(model);
	}

	public boolean hasVoidModelConst() {
		return FeatureUtils.hasVoidModelConst(model);
	}

	public boolean hasRedundantConst() {
		return FeatureUtils.hasRedundantConst(model);
	}

	public boolean hasFalseOptionalFeatures() {
		return FeatureUtils.hasFalseOptionalFeatures(model);
	}

	public void setUndoContext(Object undoContext) {
		FeatureUtils.setUndoContext(model, undoContext);
	}

	public Object getUndoContext() {
		return FeatureUtils.getUndoContext(model);
	}

	public List<String> getFeatureOrderList() {
		return Functional.toList(FeatureUtils.getFeatureOrderList(model));
	}

	public void setFeatureOrderList(final List<String> featureOrderList) {
		FeatureUtils.setFeatureOrderList(model, featureOrderList);
	}

	public boolean isFeatureOrderUserDefined() {
		return FeatureUtils.isFeatureOrderUserDefined(model);
	}

	public void setFeatureOrderUserDefined(boolean featureOrderUserDefined) {
		FeatureUtils.setFeatureOrderUserDefined(model, featureOrderUserDefined);
	}

	public boolean isFeatureOrderInXML() {
		return FeatureUtils.isFeatureOrderInXML(model);
	}

	public void setFeatureOrderInXML(boolean featureOrderInXML) {
		FeatureUtils.setFeatureOrderInXML(model, featureOrderInXML);
	}

	@Override
	public String toString() {
		return FeatureUtils.toString(model);
	}

	@Override
	public boolean equals(Object obj) {
		return FeatureUtils.equals(model, obj);
	}

	@Override
	public int hashCode() {
		return FeatureUtils.hashCode(model);
	}

	@Override
	public GraphicItem getItemType() {
		return FeatureUtils.getItemType(model);
	}

}
