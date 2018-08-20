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
package de.ovgu.featureide.fm.core.base;

import static de.ovgu.featureide.fm.core.functional.Functional.filter;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Hashtable;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.SatSolver;
import org.prop4j.solver.SatInstance;

import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureConnection;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.Features;
import de.ovgu.featureide.fm.core.IFeatureModelLayout;
import de.ovgu.featureide.fm.core.IGraphicItem.GraphicItem;
import de.ovgu.featureide.fm.core.Operator;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.conf.IFeatureGraph;
import de.ovgu.featureide.fm.core.filter.ConcreteFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;

/**
 * Several convenience methods for handling feature models, features and constraints.
 *
 * @author Marcus Pinnecke
 */
public final class FeatureUtils {

	public static final IFunction<CharSequence, String> CHARSQUENCE_TO_STRING = new IFunction<CharSequence, String>() {

		@Override
		public String invoke(CharSequence t) {
			requireNonNull(t);

			return t.toString();
		}

	};

	public static final ConcreteFeatureFilter CONCRETE_FEATURE_FILTER = new ConcreteFeatureFilter();

	public static final IFunction<IConstraint, Node> CONSTRAINT_TO_NODE = new IFunction<IConstraint, Node>() {

		@Override
		public Node invoke(IConstraint t) {
			requireNonNull(t);

			return t.getNode();
		}

	};

	public static final IFunction<IFeature, IFeatureStructure> FEATURE_TO_STRUCTURE = new IFunction<IFeature, IFeatureStructure>() {

		@Override
		public IFeatureStructure invoke(IFeature t) {
			requireNonNull(t);

			return t.getStructure();
		}
	};

	public static final IFunction<IFeature, String> GET_FEATURE_NAME = new IFunction<IFeature, String>() {

		@Override
		public String invoke(IFeature t) {
			return t.getName();
		}
	};

	public static final IFunction<IFeatureStructure, IFeature> STRUCTURE_TO_FEATURE = new IFunction<IFeatureStructure, IFeature>() {

		@Override
		public IFeature invoke(IFeatureStructure t) {
			requireNonNull(t);

			return t.getFeature();
		}
	};

	public static final void addAnnotation(IFeatureModel featureModel, CharSequence annotation) {
		requireNonNull(featureModel);
		requireNonNull(annotation);

		featureModel.getProperty().addAnnotation(annotation);
	}

	public static final void addChild(IFeature feature, IFeature newChild) {
		requireNonNull(feature);
		requireNonNull(newChild);

		feature.getStructure().addChild(newChild.getStructure());
	}

	public static final void addChildAtPosition(IFeature feature, int index, IFeature newChild) {
		requireNonNull(feature);
		requireNonNull(newChild);

		feature.getStructure().addChildAtPosition(index, newChild.getStructure());
	}

	public static final void addComment(IFeatureModel featureModel, CharSequence comment) {
		requireNonNull(featureModel);
		requireNonNull(comment);

		featureModel.getProperty().addComment(comment);
	}

	public static final void addConstraint(IFeatureModel featureModel, IConstraint constraint) {
		requireNonNull(featureModel);
		requireNonNull(constraint);

		featureModel.addConstraint(constraint);
	}

	public static final void addConstraint(IFeatureModel featureModel, IConstraint constraint, int index) {
		requireNonNull(featureModel);
		requireNonNull(constraint);

		featureModel.addConstraint(constraint, index);
	}

	public static final boolean addFeature(IFeatureModel featureModel, IFeature feature) {
		requireNonNull(featureModel);
		requireNonNull(feature);

		return featureModel.addFeature(feature);
	}

	public static final void addListener(IConstraint constraint, PropertyChangeListener listener) {
		// constraint.addListener(listener);
	}

	public static final void addListener(IFeature feature, PropertyChangeListener listener) {
		// feature.addListener(listener);
	}

	public static final void addListener(IFeatureModel featureModel, PropertyChangeListener listener) {
		// featureModel.addListener(listener);
	}

	public static final void addPropositionalNode(IFeatureModel featureModel, Node node) {
		requireNonNull(featureModel);
		requireNonNull(node);

		featureModel.addConstraint(new Constraint(featureModel, node));
	}

	public static final void addPropositionalNode(IFeatureModel featureModel, Node node, int index) {
		requireNonNull(featureModel);
		requireNonNull(node);

		featureModel.addConstraint(new Constraint(featureModel, node), index);
	}

	public static final void addTargetConnection(IFeature feature, FeatureConnection connection) {
		// feature.getStructure().addTargetConnection(connection);
	}

	public static final void changeToAlternative(IFeature feature) {
		requireNonNull(feature);

		feature.getStructure().changeToAlternative();
	}

	public static final void changeToAnd(IFeature feature) {
		requireNonNull(feature);

		feature.getStructure().changeToAnd();
	}

	public static final void changeToOr(IFeature feature) {
		requireNonNull(feature);

		feature.getStructure().changeToOr();
	}

	public static final IFeature clone(IFeature feature) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	public static final IFeature clone(IFeature feature, IFeatureModel featureModel, boolean complete) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	public static final IFeatureModel clone(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.clone();
	}

	public static Iterable<IFeature> convertToFeatureIteration(List<IFeatureStructure> list) {
		requireNonNull(list);

		return Functional.map(list, STRUCTURE_TO_FEATURE);
	}

	public static List<IFeature> convertToFeatureList(List<IFeatureStructure> list) {
		requireNonNull(list);

		return Functional.toList(Functional.map(list, STRUCTURE_TO_FEATURE));
	}

	public static Iterable<IFeatureStructure> convertToFeatureStructureList(List<IFeature> list) {
		requireNonNull(list);

		return Functional.map(list, FEATURE_TO_STRUCTURE);
	}

	public static final FeatureModelAnalyzer createAnalyser(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getAnalyser();
	}

	public static final void createDefaultValues(IFeatureModel featureModel, CharSequence projectName) {
		requireNonNull(featureModel);
		requireNonNull(projectName);

		featureModel.createDefaultValues(projectName);
	}

	public static final boolean deleteFeature(IFeatureModel featureModel, IFeature feature) {
		requireNonNull(featureModel);
		requireNonNull(feature);

		return featureModel.deleteFeature(feature);
	}

	public static final void deleteFeatureFromTable(IFeatureModel featureModel, IFeature feature) {
		requireNonNull(featureModel);
		requireNonNull(feature);

		featureModel.deleteFeatureFromTable(feature);
	}

	public static final boolean equals(IConstraint constraint, Object obj) {
		requireNonNull(constraint);
		requireNonNull(obj);

		return constraint.equals(obj);
	}

	public static final boolean equals(IFeatureModel featureModel, Object obj) {
		requireNonNull(featureModel);
		requireNonNull(obj);

		return featureModel.equals(obj);
	}

	/**
	 * Extracts all concrete features from a feature model by calling {@link #extractConcreteFeatures(Iterable)} on <code>model.getFeatures()</code>.
	 *
	 * @since 3.0
	 * @param model A feature model
	 * @author Marcus Pinnecke
	 * @return An iterable object that yields all concrete features of <b>features</b>
	 */
	public static Iterable<IFeature> extractConcreteFeatures(final IFeatureModel model) {
		requireNonNull(model);

		return extractConcreteFeatures(model.getFeatures());
	}

	/**
	 * Extracts all concrete features from an object that yields features. Basically, an invocation of this method on <b>features</b> will return an iterable
	 * object that yields a feature <i>f</i> from <b>features</b> if and only if <i>f</i> is concrete. Since the implementation based on iterators, it is a lazy
	 * filtering without modification of <b>features</b>.
	 *
	 * <br/> <br/> The extraction is done via
	 * {@link de.ovgu.featureide.fm.core.functional.Functional#filter(Iterable, de.ovgu.featureide.fm.core.filter.base.IFilter)}
	 *
	 * @since 3.0
	 * @param features An iterable object providing features
	 * @author Marcus Pinnecke
	 * @return An iterable object that yields all concrete features of <b>features</b>
	 */
	public static Iterable<IFeature> extractConcreteFeatures(final Iterable<IFeature> features) {
		requireNonNull(features);

		return filter(features, CONCRETE_FEATURE_FILTER);
	}

	/**
	 * Extracts all concrete features from a feature model as a list of strings by calling
	 * {@link de.ovgu.featureide.fm.core.functional.Functional#mapToStringList(Iterable)} on the result of {@link #extractConcreteFeatures(IFeatureModel)} using
	 * <code>model.getFeatures()</code>.
	 *
	 * @since 3.0
	 * @param model A feature model
	 * @author Marcus Pinnecke
	 * @return A list of strings that contains the feature names of all concrete features of <b>features</b>
	 */
	public static List<String> extractConcreteFeaturesAsStringList(IFeatureModel model) {
		requireNonNull(model);

		return new ArrayList<String>(Functional.mapToStringList(FeatureUtils.extractConcreteFeatures(model.getFeatures())));
	}

	public static Iterable<String> extractFeatureNames(Collection<IFeature> features) {
		requireNonNull(features);

		return Functional.map(features, GET_FEATURE_NAME);
	}

	public static Iterable<String> extractFeatureNames(Iterable<IFeature> features) {
		requireNonNull(features);

		return Functional.map(features, GET_FEATURE_NAME);
	}

	public static final List<String> getExplicitFeatureList(IFeatureModel featureModel) {
		final List<String> featureList = getFeatureNamesList(featureModel);
		final ArrayList<String> result = new ArrayList<String>();
		for (final String s : featureList) {
			result.add(s + " " + Features.FEATURE_SUFFIX);
		}
		return result;
	}

	public static final void fire(IConstraint constraint, PropertyChangeEvent event) {
		// constraint.fireEvent(event);
	}

	public static final void fire(IFeature feature, PropertyChangeEvent event) {
		requireNonNull(feature);
		requireNonNull(event);

		// feature.fireEvent(event);
	}

	public static final FeatureModelAnalyzer getAnalyser(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getAnalyser();
	}

	public static final List<String> getAnnotations(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(featureModel.getProperty().getAnnotations());
	}

	public static int getChildIndex(IFeature feature, IFeature child) {
		requireNonNull(feature);
		requireNonNull(child);

		return feature.getStructure().getChildIndex(child.getStructure());
	}

	public static final Iterable<IFeature> getChildren(IFeature feature) {
		requireNonNull(feature);

		return Functional.map(feature.getStructure().getChildren(), STRUCTURE_TO_FEATURE);
	}

	public static final int getChildrenCount(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().getChildrenCount();
	}

	public static final ColorList getColorList(IFeature feature) {
		// return feature.getGraphicRepresenation().getColorList();
		return null;
	}

	public static final ColorschemeTable getColorschemeTable(IFeatureModel featureModel) {
		// return featureModel.getGraphicRepresenation().getColorschemeTable();
		return null;
	}

	public static final List<String> getComments(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(featureModel.getProperty().getComments());
	}

	@Nonnull
	public static final Iterable<String> getConcreteFeatureNames(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return FeatureUtils.extractConcreteFeaturesAsStringList(featureModel);
	}

	@Nonnull
	public static final Collection<IFeature> getConcreteFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(FeatureUtils.extractConcreteFeatures(featureModel));
	}

	public static final Node getConstraint(IFeatureModel featureModel, int index) {
		requireNonNull(featureModel);

		return Functional.toList(getPropositionalNodes(featureModel)).get(index);
	}

	public static final ConstraintAttribute getConstraintAttribute(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.getConstraintAttribute();
	}

	public static final int getConstraintCount(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getConstraintCount();
	}

	public static final int getConstraintIndex(IFeatureModel featureModel, IConstraint constraint) {
		requireNonNull(featureModel);
		requireNonNull(constraint);

		final List<IConstraint> constraints = featureModel.getConstraints();
		for (int i = 0; i < constraints.size(); i++) {
			if (constraints.get(i).equals(constraint)) {
				return i;
			}
		}
		throw new NoSuchElementException();
	}

	public static final List<IConstraint> getConstraints(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getConstraints();
	}

	public static final Collection<IFeature> getContainedFeatures(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.getContainedFeatures();
	}

	public static final Collection<IFeature> getDeadFeatures(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.getDeadFeatures();
	}

	public static final Collection<IFeature> getDeadFeatures(IConstraint constraint, IFeatureModel fm, Collection<IFeature> fmDeadFeatures) {
		requireNonNull(constraint);
		requireNonNull(fmDeadFeatures);

		Collection<IFeature> deadFeaturesBefore = null;
		final Node propNode = constraint.getNode();
		if (propNode != null) {
			fm.removeConstraint(constraint);
			deadFeaturesBefore = fm.getAnalyser().getDeadFeatures();
			fm.addConstraint(new Constraint(fm, propNode));
			fm.handleModelDataChanged();
		}

		final Collection<IFeature> deadFeaturesAfter = new LinkedList<IFeature>();
		for (final IFeature f : fmDeadFeatures) {
			final IFeature feature = fm.getFeature(f.getName());
			// XXX why can the given feature not be found?
			if ((feature != null) && !deadFeaturesBefore.contains(feature)) {
				deadFeaturesAfter.add(f);
			}
		}
		return deadFeaturesAfter;
	}

	public static final Collection<IFeature> getDeadFeatures(IConstraint constraint, SatSolver solver, IFeatureModel fm, Collection<IFeature> fmDeadFeatures) {
		requireNonNull(constraint);
		requireNonNull(fmDeadFeatures);

		return Functional.toList(constraint.getDeadFeatures(solver, fm, fmDeadFeatures));
	}

	public static final String getDescription(IFeature feature) {
		requireNonNull(feature);

		return feature.getProperty().getDescription();
	}

	@Deprecated
	public static final String getDisplayName(IFeature feature) {
		requireNonNull(feature);

		return feature.getProperty().getDisplayName();
	}

	public static final Iterable<IFeature> getFalseOptional(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.getFalseOptional();
	}

	public static final IFeature getFeature(IFeatureModel featureModel, CharSequence name) {
		requireNonNull(featureModel);
		requireNonNull(name);

		return featureModel.getFeature(name.toString());
	}

	public static final IFeatureModel getFeatureModel(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.getFeatureModel();
	}

	public static final IFeatureModel getFeatureModel(IFeature feature) {
		requireNonNull(feature);

		return feature.getFeatureModel();
	}

	public static final Set<String> getFeatureNames(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toSet(FeatureUtils.extractFeatureNames(featureModel.getFeatures()));
	}

	public static final List<String> getFeatureNamesList(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getFeatures()));
	}

	public static final List<String> getFeatureNamesPreorder(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getStructure().getFeaturesPreorder()));
	}

	public static final Collection<String> getFeatureOrderList(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getFeatureOrderList();
	}

	public static final Collection<IFeature> getFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(featureModel.getFeatures());
	}

	public static final Collection<IFeature> getFeaturesPreorder(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().getFeaturesPreorder();
	}

	public static final FeatureStatus getFeatureStatus(IFeature feature) {
		requireNonNull(feature);

		return feature.getProperty().getFeatureStatus();
	}

	public static final Map<String, IFeature> getFeatureTable(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getFeatureTable();
	}

	public static final IFeature getFirstChild(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().getFirstChild().getFeature();
	}

	public static final GraphicItem getItemType(IConstraint constraint) {
		// return constraint.getGraphicRepresenation().getItemType();
		return null;
	}

	public static final GraphicItem getItemType(IFeature feature) {
		// return feature.getGraphicRepresenation().getItemType();
		return null;
	}

	public static final GraphicItem getItemType(IFeatureModel featureModel) {
		// return featureModel.getGraphicRepresenation().getItemType();
		return null;
	}

	public static final IFeature getLastChild(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().getLastChild().getFeature();
	}

	public static final IFeatureModelLayout getLayout(IFeatureModel featureModel) {
		// return featureModel.getLayout();
		return null;
	}

	public static final String getName(IFeature feature) {
		requireNonNull(feature);

		return feature.getName();
	}

	public static final Node getNode(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.getNode();
	}

	public static final int getNumberOfFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getNumberOfFeatures();
	}

	/**
	 * Returns the direct parent of the given feature.
	 *
	 * @param feature the feature to check
	 * @return the direct parent; null if there is no parent
	 */
	@CheckForNull
	public static final IFeature getParent(IFeature feature) {
		if (feature != null) {
			final IFeatureStructure parent = feature.getStructure().getParent();
			if (parent != null) {
				return parent.getFeature();
			}
		}
		return null;
	}

	/**
	 * Returns all parents of the given feature recursively.
	 *
	 * @param feature the feature to check
	 * @return all parents; not null
	 */
	public static Set<IFeature> getParents(IFeature feature) {
		if (feature == null) {
			return Collections.emptySet();
		}
		return getParents(feature, new LinkedHashSet<IFeature>());
	}

	/**
	 * Returns all parents of all the given features recursively.
	 *
	 * @param features the features to check
	 * @return all parents; not null
	 */
	public static Set<IFeature> getParents(Collection<? extends IFeature> features) {
		if ((features == null) || features.isEmpty()) {
			return Collections.emptySet();
		}
		final Set<IFeature> parents = new LinkedHashSet<>();
		for (final IFeature feature : features) {
			getParents(feature, parents);
		}
		return parents;
	}

	/**
	 * Returns all parents of the given feature recursively.
	 *
	 * @param feature the feature to check
	 * @param parents previously found parents; out variable; not null
	 * @return all parents; not null
	 */
	private static Set<IFeature> getParents(IFeature feature, Set<IFeature> parents) {
		while (true) {
			final IFeature parent = getParent(feature);
			if ((parent == null) || !parents.add(parent)) { // parent missing or already found before
				break;
			}
			feature = parent;
		}
		return parents;
	}

	public static final Iterable<Node> getPropositionalNodes(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.map(featureModel.getConstraints(), CONSTRAINT_TO_NODE);
	}

	public static Iterable<Node> getPropositionalNodes(Iterable<IConstraint> constraints) {
		requireNonNull(constraints);

		return Functional.toList(Functional.map(constraints, CONSTRAINT_TO_NODE));
	}

	public static final Collection<IConstraint> getRelevantConstraints(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().getRelevantConstraints();
	}

	public static final String getRelevantConstraintsString(IFeature feature) {
		requireNonNull(feature);

		return FeatureUtils.getRelevantConstraintsString(feature, feature.getFeatureModel().getConstraints());
	}

	public static String getRelevantConstraintsString(IFeature feature, Collection<IConstraint> constraints) {
		requireNonNull(feature);
		requireNonNull(constraints);

		final StringBuilder relevant = new StringBuilder();
		for (final IConstraint constraint : constraints) {
			for (final IFeature f : constraint.getContainedFeatures()) {
				if ((f != null) && f.getName().equals(feature.getName())) {
					relevant.append((relevant.length() == 0 ? "" : "\n") + "\u2022 " + constraint.getNode().toString(NodeWriter.logicalSymbols) + " ");
					break;
				}
			}
		}
		return relevant.toString();
	}

	public static final RenamingsManager getRenamingsManager(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getRenamingsManager();
	}

	public static final IFeature getRoot(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		final IFeatureStructure root = featureModel.getStructure().getRoot();
		if (root != null) {
			return root.getFeature();
		}
		return null;
	}

	public static final Iterable<FeatureConnection> getSourceConnections(IFeature feature) {
		// return feature.getStructure().getSourceConnections();
		return null;
	}

	public static final Iterable<FeatureConnection> getTargetConnections(IFeature feature) {
		// return feature.getStructure().getTargetConnections();
		return null;
	}

	public static final void handleLegendLayoutChanged(IFeatureModel featureModel) {
		// featureModel.getGraphicRepresenation().handleLegendLayoutChanged();
	}

	public static final void handleModelDataChanged(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		featureModel.handleModelDataChanged();
	}

	public static final void handleModelDataLoaded(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		featureModel.handleModelDataLoaded();
	}

	public static final void handleModelLayoutChanged(IFeatureModel featureModel) {
		// featureModel.getGraphicRepresenation().handleModelLayoutChanged();
	}

	public static final boolean hasAbstract(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasAbstract();
	}

	public static final boolean hasAlternativeGroup(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasAlternativeGroup();
	}

	public static final boolean hasAndGroup(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasAndGroup();
	}

	public static final boolean hasChildren(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().hasChildren();
	}

	public static final boolean hasConcrete(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasConcrete();
	}

	public static final boolean hasDeadConst(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasDeadConstraints();
	}

	public static final boolean hasFalseOptionalFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasFalseOptionalFeatures();
	}

	public static final int hashCode(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.hashCode();
	}

	public static final int hashCode(IFeature feature) {
		requireNonNull(feature);

		return feature.hashCode();
	}

	public static final int hashCode(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.hashCode();
	}

	public static final boolean hasHidden(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasHidden();
	}

	public static final boolean hasHiddenFeatures(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.hasHiddenFeatures();
	}

	public static final boolean hasHiddenParent(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().hasHiddenParent();
	}

	public static final boolean hasIndetHidden(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasIndetHidden();
	}

	public static final boolean hasInlineRule(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().hasInlineRule();
	}

	public static final boolean hasMandatoryFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasMandatoryFeatures();
	}

	public static final boolean hasOptionalFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasOptionalFeatures();
	}

	public static final boolean hasOrGroup(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasOrGroup();
	}

	public static final boolean hasRedundantConst(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasRedundantConstraints();
	}

	public static final boolean hasTautologyConst(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasTautologyConstraints();
	}

	public static final boolean hasUnsatisfiableConst(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasUnsatisfiableConstraints();
	}

	public static final boolean hasVoidModelConst(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasVoidModelConstraints();
	}

	public static final boolean isAbstract(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isAbstract();
	}

	public static final boolean isAlternative(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isAlternative();
	}

	public static final boolean isAncestorOf(IFeature feature, IFeature next) {
		requireNonNull(feature);
		requireNonNull(next);

		return feature.getStructure().isAncestorOf(next.getStructure());
	}

	public static final boolean isAnd(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isAnd();
	}

	public static final boolean isANDPossible(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isANDPossible();
	}

	public static final boolean isConcrete(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isConcrete();
	}

	@Deprecated
	public static final boolean isConcrete(IFeatureModel featureModel, CharSequence featureName) {
		requireNonNull(featureModel);
		requireNonNull(featureName);

		for (final IFeature feature : FeatureUtils.extractConcreteFeatures(featureModel)) {
			if (feature.getName().equals(featureName)) {
				return true;
			}
		}
		return false;
	}

	public static final boolean isConstraintSelected(IFeature feature) {
		requireNonNull(feature);

		return feature.getProperty().isConstraintSelected();
	}

	public static final boolean isFeatureOrderUserDefined(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.isFeatureOrderUserDefined();
	}

	public static final boolean isFirstChild(IFeature feature, IFeature child) {
		requireNonNull(feature);
		requireNonNull(child);

		return feature.getStructure().isFirstChild(child.getStructure());
	}

	public static final boolean isHidden(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isHidden();
	}

	public static final boolean isMandatory(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isMandatory();
	}

	public static final boolean isMandatorySet(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isMandatorySet();
	}

	public static final boolean isMultiple(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isMultiple();
	}

	public static final boolean isOr(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isOr();
	}

	public static final boolean isRoot(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().isRoot();
	}

	public static final int numAlternativeGroup(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().numAlternativeGroup();
	}

	public static final int numOrGroup(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().numOrGroup();
	}

	public static void print(IFeature feature, StringBuilder string) {
		requireNonNull(feature);
		requireNonNull(string);

		string.append(feature.getName());
		string.append(", mandatory=" + FeatureUtils.isMandatory(feature));
		final List<IFeatureStructure> struct = feature.getStructure().getChildren();
		final boolean isLeaf = struct.isEmpty();
		if (!isLeaf) {
			final String prop = FeatureUtils.isOr(feature) ? " or" : FeatureUtils.isAlternative(feature) ? " alt" : " and";
			string.append(" " + prop);
			string.append("[");
			for (int i = 0; i < struct.size(); i++) {
				print(struct.get(i).getFeature(), string);
				if ((i + 1) < struct.size()) {
					string.append(", ");
				}
			}
			string.append("]");
		}
	}

	public static final void propertyChange(IFeature feature, PropertyChangeEvent event) {
		requireNonNull(feature);
		requireNonNull(event);

		throw new UnsupportedOperationException("Not implemented yet");
	}

	public static final void redrawDiagram(IFeatureModel featureModel) {
		// featureModel.getGraphicRepresenation().redrawDiagram();
	}

	public static final void refreshContextMenu(IFeatureModel featureModel) {
		// featureModel.getGraphicRepresenation().refreshContextMenu();
	}

	public static final void removeChild(IFeature feature, IFeature child) {
		requireNonNull(feature);
		requireNonNull(child);

		feature.getStructure().removeChild(child.getStructure());
	}

	public static final void removeConstraint(IFeatureModel featureModel, IConstraint constraint) {
		requireNonNull(featureModel);
		requireNonNull(constraint);

		final List<IConstraint> constraints = featureModel.getConstraints();
		final int index = getConstraintIndex(featureModel, constraint);
		tryRemoveConstraint(featureModel, constraints, index);
	}

	public static final void removeConstraint(IFeatureModel featureModel, int index) {
		requireNonNull(featureModel);

		tryRemoveConstraint(featureModel, featureModel.getConstraints(), index);
	}

	public static final IFeature removeLastChild(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().removeLastChild().getFeature();
	}

	public static final void removeListener(IConstraint constraint, PropertyChangeListener listener) {
		// constraint.removeListener(listener);
	}

	public static final void removeListener(IFeature feature, PropertyChangeListener listener) {
		// feature.removeListener(listener);
	}

	public static final void removeListener(IFeatureModel featureModel, PropertyChangeListener listener) {
		// featureModel.removeListener(listener);
	}

	public static final void removePropositionalNode(IFeatureModel featureModel, Node node) {
		requireNonNull(featureModel);
		requireNonNull(node);

		final List<IConstraint> constraints = featureModel.getConstraints();
		int index = -1;
		for (int i = 0; i < constraints.size(); i++) {
			if (constraints.get(i).getNode().equals(node)) {
				index = i;
				break;
			}
		}
		tryRemoveConstraint(featureModel, new LinkedList<>(constraints), index);
	}

	public static final boolean removeTargetConnection(IFeature feature, FeatureConnection connection) {
		// return feature.getStructure().removeTargetConnection(connection);
		return false;
	}

	public static final void replaceChild(IFeature feature, IFeature oldChild, IFeature newChild) {
		requireNonNull(feature);
		requireNonNull(oldChild);
		requireNonNull(newChild);

		feature.getStructure().replaceChild(oldChild.getStructure(), newChild.getStructure());
	}

	public static void replacePropNode(IFeatureModel featureModel, int index, Node propNode) {
		requireNonNull(featureModel);
		requireNonNull(propNode);

		featureModel.setConstraint(index, new Constraint(featureModel, propNode));
	}

	public static final void replaceRoot(IFeatureModel featureModel, IFeature feature) {
		requireNonNull(featureModel);
		requireNonNull(feature);

		featureModel.getStructure().replaceRoot(feature.getStructure());
	}

	public static final void requireNonNull(Object object) {
		// TODO check unnecessary null checks, may cuase defect itself
		// or move to constructors
		// java.util.Objects.requireNonNull(object, StringTable.PARAMETER_IS_EXPECTED_TO_BE_NON_NULL);
	}

	public static final void reset(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		featureModel.reset();
	}

	public static final void setAbstract(IFeature feature, boolean value) {
		requireNonNull(feature);

		feature.getStructure().setAbstract(value);
	}

	public static final void setAlternative(IFeature feature) {
		requireNonNull(feature);

		feature.getStructure().setAlternative();
	}

	// public static final void setUndoContext(IFeatureModel featureModel, Object undoContext) {
	// featureModel.getUndoContext(undoContext);
	// }
	//
	// public static final Object getUndoContext(IFeatureModel featureModel) {
	// return featureModel.getUndoContext();
	// }

	public static final void setAnd(IFeature feature) {
		requireNonNull(feature);

		feature.getStructure().setAnd();
	}

	public static void setAnd(IFeature feature, boolean and) {
		requireNonNull(feature);

		feature.getStructure().setAND(and);
	}

	public static final void setAND(IFeature feature, boolean and) {
		requireNonNull(feature);

		feature.getStructure().setAND(and);
	}

	public static final void setChildren(IFeature feature, Iterable<IFeature> children) {
		requireNonNull(children);

		feature.getStructure().setChildren(Functional.toList(Functional.map(children, FEATURE_TO_STRUCTURE)));
	}

	// public static final boolean isFeatureOrderInXML(IFeatureModel featureModel) {
	// return featureModel.isFeatureOrderInXML();
	// }
	//
	// public static final void setFeatureOrderInXML(IFeatureModel featureModel, boolean featureOrderInXML) {
	// featureModel.setFeatureOrderInXML(featureModel, featureOrderInXML);
	// }

	public static final void setConstraintAttribute(IConstraint constraint, ConstraintAttribute attri, boolean fire) {
		requireNonNull(constraint);
		requireNonNull(attri);

		constraint.setConstraintAttribute(attri, fire);
	}

	public static final void setConstraints(IFeatureModel featureModel, final Iterable<IConstraint> constraints) {
		requireNonNull(featureModel);
		requireNonNull(constraints);

		featureModel.setConstraints(constraints);
	}

	public static final void setConstraintSelected(IFeature feature, boolean selection) {
		requireNonNull(feature);

		feature.getProperty().selectConstraint(selection);
	}

	public static final void setContainedFeatures(IConstraint constraint) {
		requireNonNull(constraint);

		constraint.setContainedFeatures();
	}

	public static final void setDeadFeatures(IConstraint constraint, Collection<IFeature> deadFeatures) {
		requireNonNull(constraint);
		requireNonNull(deadFeatures);

		constraint.setDeadFeatures(deadFeatures);
	}

	public static final void setDescription(IFeature feature, CharSequence description) {
		requireNonNull(feature);
		requireNonNull(description);

		feature.getProperty().setDescription(description);
	}

	public static final boolean setFalseOptionalFeatures(IConstraint constraint) {
		requireNonNull(constraint);

		boolean found = false;

		final Collection<IFeature> falseOptionalFeatures = new ArrayList<>();
		final IFeatureModel featureModel = constraint.getFeatureModel();
		final IFeatureModel clonedModel = FeatureUtils.clone(constraint.getFeatureModel());
		clonedModel.removeConstraint(constraint);
		final Collection<IFeature> foFeatures = clonedModel.getAnalyser().getFalseOptionalFeatures();
		for (final IFeature feature : featureModel.getAnalyser().getFalseOptionalFeatures()) {
			if (!foFeatures.contains(clonedModel.getFeature(feature.getName())) && !falseOptionalFeatures.contains(feature)) {
				falseOptionalFeatures.add(feature);
				found = true;
			}
		}
		return found;
	}

	public static final boolean setFalseOptionalFeatures(IConstraint constraint, IFeatureModel clone, Collection<IFeature> fmFalseOptionals) {
		requireNonNull(constraint);
		requireNonNull(fmFalseOptionals);

		return constraint.setFalseOptionalFeatures(clone, fmFalseOptionals);
	}

	public static final void setFeatureOrderList(IFeatureModel featureModel, final List<String> featureOrderList) {
		requireNonNull(featureModel);
		requireNonNull(featureOrderList);

		featureModel.setFeatureOrderList(featureOrderList);
	}

	public static final void setFeatureOrderUserDefined(IFeatureModel featureModel, boolean featureOrderUserDefined) {
		requireNonNull(featureModel);

		featureModel.setFeatureOrderUserDefined(featureOrderUserDefined);
	}

	public static final void setFeatureStatus(IFeature feature, FeatureStatus stat, boolean fire) {
		requireNonNull(feature);
		requireNonNull(stat);

		feature.getProperty().setFeatureStatus(stat, fire);
	}

	public static final void setFeatureTable(IFeatureModel featureModel, final Hashtable<String, IFeature> featureTable) {
		requireNonNull(featureModel);
		requireNonNull(featureTable);

		featureModel.setFeatureTable(featureTable);
	}

	public static void setHiddden(IFeature feature, boolean hid) {
		requireNonNull(feature);

		feature.getStructure().setHidden(hid);
	}

	public static final void setHidden(IFeature feature, boolean hid) {
		requireNonNull(feature);

		feature.getStructure().setHidden(hid);
	}

	public static final void setMandatory(IFeature feature, boolean mandatory) {
		requireNonNull(feature);

		feature.getStructure().setMandatory(mandatory);
	}

	public static final void setMultiple(IFeature feature, boolean multiple) {
		requireNonNull(feature);

		feature.getStructure().setMultiple(multiple);
	}

	public static final void setName(IFeature feature, String name) {
		requireNonNull(feature);

		feature.setName(name);
	}

	public static final void setOr(IFeature feature) {
		requireNonNull(feature);

		feature.getStructure().setOr();
	}

	public static final void setParent(IFeature feature, IFeature newParent) {
		requireNonNull(feature);
		requireNonNull(newParent);

		feature.getStructure().setParent(newParent.getStructure());
	}

	public static void setRelevantConstraints(IFeature bone) {
		requireNonNull(bone);

		final List<IConstraint> constraintList = new LinkedList<>();
		for (final IConstraint constraint : bone.getFeatureModel().getConstraints()) {
			for (final IFeature f : constraint.getContainedFeatures()) {
				if (f.getName().equals(bone.getName())) {
					constraintList.add(constraint.clone(bone.getFeatureModel()));
					break;
				}
			}
		}
		bone.getStructure().setRelevantConstraints(constraintList);
	}

	public static final void setRoot(IFeatureModel featureModel, IFeature root) {
		requireNonNull(featureModel);
		requireNonNull(root);

		featureModel.getStructure().setRoot(root.getStructure());
	}

	public static final String toString(IConstraint constraint) {
		requireNonNull(constraint);

		return constraint.toString();
	}

	public static final String toString(IFeature feature) {
		requireNonNull(feature);

		return feature.toString();
	}

	public static final String toString(IFeature feature, boolean writeMarks) {
		requireNonNull(feature);

		if (writeMarks) {
			final String featureName = feature.getName();
			if (featureName.contains(" ") || Operator.isOperatorName(featureName)) {
				return "\"" + feature.getName() + "\"";
			}
			return feature.getName();
		} else {
			return feature.toString();
		}
	}

	public static final String toString(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.toString();
	}

	private static void tryRemoveConstraint(IFeatureModel featureModel, List<IConstraint> constraints, int index) {
		requireNonNull(featureModel);
		requireNonNull(constraints);

		if ((index == -1) || (index >= constraints.size())) {
			throw new NoSuchElementException();
		} else {
			constraints.remove(index);
			featureModel.setConstraints(constraints);
		}
	}

	private FeatureUtils() {}

	public CharSequence createValidJavaIdentifierFromString(CharSequence s) {
		requireNonNull(s);

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

	public static String[] getFeaturesFromFeatureGraph(IFeatureGraph featureGraph) {
		final SatInstance satInstance = featureGraph.getSatInstance();
		final String[] featureNames = new String[satInstance.getNumberOfVariables()];

		for (int i = 0; i < featureNames.length; i++) {
			featureNames[i] = (String) satInstance.getVariableObject(i + 1);
		}
		return featureNames;
	}

	public static String[] getCoreFeaturesFromFeatureGraph(IFeatureGraph featureGraph) {
		return getNonCommonFeaturesFromFeatureGraph(featureGraph, -1);
	}

	public static String[] getDeadFeaturesFromFeatureGraph(IFeatureGraph featureGraph) {
		return getNonCommonFeaturesFromFeatureGraph(featureGraph, -2);
	}

	private static String[] getNonCommonFeaturesFromFeatureGraph(IFeatureGraph featureGraph, int mode) {
		final SatInstance satInstance = featureGraph.getSatInstance();
		final ArrayList<String> featureNames = new ArrayList<>(satInstance.getNumberOfVariables());

		final int[] index = featureGraph.getIndex();
		for (int i = 0; i < index.length; i++) {
			if (index[i] == mode) {
				featureNames.add((String) satInstance.getVariableObject(i + 1));
			}
		}
		return featureNames.toArray(new String[0]);
	}

}
