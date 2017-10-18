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
package de.ovgu.featureide.fm.core;

import static de.ovgu.featureide.fm.core.base.FeatureUtilsLegacy.convert;

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
import de.ovgu.featureide.fm.core.base.FeatureUtilsLegacy;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * The model representation of the feature tree that notifies listeners of changes in the tree.
 *
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 *
 */
@Deprecated
public class FeatureModel extends DeprecatedFeatureModel implements IGraphicItem, Cloneable {

	public IFeatureModel model;

	public FeatureModel() {
		throw new RuntimeException("Do not use this construction any longer. Use direct assigment to member 'model' instead");
	}

	public FeatureModel(IFeatureModel model) {
		this.model = model;
	}

	protected FeatureModel(FeatureModel oldFeatureModel, boolean complete) {
		model = oldFeatureModel.model.clone();
	}

	protected FeatureModelAnalyzer createAnalyser() {
		return model.getAnalyser();
	}

	/**
	 * Returns the {@link FeatureModelAnalyzer} which should be used for all calculation on the {@link FeatureModel}.
	 */
	@Override
	public FeatureModelAnalyzer getAnalyser() {
		return model.getAnalyser();
	}

	@Override
	public IFeatureModelLayout getLayout() {
		// return model.getLayout();
		return null;
	}

	public ColorschemeTable getColorschemeTable() {
		// return model.getGraphicRepresenation().getColorschemeTable();
		return null;
	}

	@Override
	public FMComposerManager getFMComposerManager(final IProject project) {
		return (FMComposerManager) FMComposerManager.getFMComposerExtension(null);
	}

	public IFMComposerExtension initFMComposerExtension(final IProject project) {
		return FMComposerManager.getFMComposerExtension(null);
	}

	public IFMComposerExtension getFMComposerExtension() {
		return FMComposerManager.getFMComposerExtension(null);
	}

	@Override
	public RenamingsManager getRenamingsManager() {
		return model.getRenamingsManager();
	}

	public void reset() {
		FeatureUtils.reset(model);
	}

	/**
	 * Creates a default {@link FeatureModel} with a root feature named as the project and a child feature named base.
	 *
	 * @param projectName The name of the project
	 */
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
		final Hashtable<String, IFeature> iFeatureTable = new Hashtable<>();
		for (final String key : Functional.toIterator(featureTable.keys())) {
			iFeatureTable.put(key, convert(featureTable.get(key)));
		}
		FeatureUtils.setFeatureTable(model, iFeatureTable);
	}

	public boolean addFeature(Feature feature) {
		return FeatureUtils.addFeature(model, convert(feature));
	}

	public Collection<Feature> getFeatures() {
		return Functional.toList(Functional.map(FeatureUtils.getFeatures(model), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	/**
	 * @return The {@link Feature} with the given name or {@code null} if there is no feature with this name.
	 */
	@CheckForNull
	public Feature getFeature(String name) {
		return FeatureUtilsLegacy.convert(FeatureUtils.getFeature(model, name));
	}

	/**
	 *
	 * @return A list of all concrete features. This list is in preorder of the tree.
	 */
	@Nonnull
	public Collection<Feature> getConcreteFeatures() {
		return Functional.toList(Functional.map(FeatureUtils.getConcreteFeatures(model), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	/**
	 *
	 * @return A list of all concrete feature names. This list is in preorder of the tree.
	 */
	@Nonnull
	public List<String> getConcreteFeatureNames() {
		return Functional.toList(FeatureUtils.getConcreteFeatureNames(model));
	}

	public Collection<Feature> getFeaturesPreorder() {
		return Functional.toList(Functional.map(FeatureUtils.getFeaturesPreorder(model), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	public List<String> getFeatureNamesPreorder() {
		return FeatureUtils.getFeatureNamesPreorder(model);
	}

	/**
	 * @return <code>true</code> if a feature with the given name exists and is concrete.
	 * @deprecated Will be removed in a future release. Use {@link #getFeature(String)}.isConcrete() instead.
	 */
	@Deprecated
	public boolean isConcrete(String featureName) {
		return FeatureUtils.isConcrete(model, featureName);
	}

	/**
	 * @return the featureTable
	 */
	protected Map<String, Feature> getFeatureTable() {
		final Map<String, Feature> result = new HashMap<>();
		final Map<String, IFeature> map = FeatureUtils.getFeatureTable(model);
		for (final String key : map.keySet()) {
			result.put(key, convert(map.get(key)));
		}
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
		FeatureUtils.setConstraints(model, Functional.map(constraints, FeatureUtilsLegacy.CONSTRAINT_TO_ICONSTRANT));
	}

	public void addPropositionalNode(Node node) {
		FeatureUtils.addPropositionalNode(model, node);
	}

	public void addConstraint(Constraint constraint) {
		FeatureUtils.addConstraint(model, convert(constraint));
	}

	public void addPropositionalNode(Node node, int index) {
		FeatureUtils.addPropositionalNode(model, node, index);
	}

	public void addConstraint(Constraint constraint, int index) {
		FeatureUtils.addConstraint(model, convert(constraint), index);
	}

	public List<Node> getPropositionalNodes() {
		return Functional.toList(FeatureUtils.getPropositionalNodes(model));
	}

	public Node getConstraint(int index) {
		return FeatureUtils.getConstraint(model, index);
	}

	public List<Constraint> getConstraints() {
		return Functional.toList(Functional.map(FeatureUtils.getConstraints(model), FeatureUtilsLegacy.ICONSTRAINT_TO_CONSTRANT));
	}

	public int getConstraintIndex(Constraint constraint) {
		return FeatureUtils.getConstraintIndex(model, convert(constraint));
	}

	public void removePropositionalNode(Node node) {
		FeatureUtils.removePropositionalNode(model, node);
	}

	public void removeConstraint(Constraint constraint) {
		FeatureUtils.removeConstraint(model, FeatureUtilsLegacy.convert(constraint));
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

	/**
	 * Refreshes the diagram colors.
	 */
	public void redrawDiagram() {
		FeatureUtils.redrawDiagram(model);
	}

	@Override
	public FeatureModel clone() {
		return new FeatureModel(model.clone());
	}

	/**
	 * Will return the value of clone(true).
	 *
	 * @return a deep copy from the feature model
	 *
	 * @see #clone(boolean)
	 */
	public FeatureModel deepClone() {
		return (FeatureModel) model.clone();
	}

	/**
	 * Clones the feature model. Makes a deep copy from all fields in the model.</br> Note that: {@code fm == fm.clone(false)} and {@code fm == fm.clone(true)}
	 * are {@code false} in every case.
	 *
	 * @param complete If {@code false} the fields annotations, comments, colorschemeTable and layout are set to {@code null} for a faster cloning process.
	 * @return a deep copy from the feature model
	 *
	 * @see #clone()
	 */
	public FeatureModel deepClone(boolean complete) {
		return (FeatureModel) model.clone();
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

	/**
	 * @return true if feature model contains or group otherwise false
	 */
	public boolean hasOrGroup() {
		return FeatureUtils.hasOrGroup(model);
	}

	public boolean hasAbstract() {
		return FeatureUtils.hasAbstract(model);
	}

	public boolean hasConcrete() {
		return FeatureUtils.hasConcrete(model);
	}

	/**
	 * @return number of or groups contained in the feature model
	 */
	public int numOrGroup() {
		return FeatureUtils.numOrGroup(model);
	}

	public int numAlternativeGroup() {
		return FeatureUtils.numAlternativeGroup(model);
	}

	/**
	 *
	 * @return <code>true</code> if the feature model contains a hidden feature
	 */
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
		// FeatureUtils.setUndoContext(model, undoContext);
	}

	public Object getUndoContext() {
		// return FeatureUtils.getUndoContext(model);
		return null;
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
		// return FeatureUtils.isFeatureOrderInXML(model);
		return false;
	}

	public void setFeatureOrderInXML(boolean featureOrderInXML) {
		// FeatureUtils.setFeatureOrderInXML(model, featureOrderInXML);
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
