/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Hashtable;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.Operator;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.filter.ConcreteFeatureFilter;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * Several convenience methods for handling feature models, features and constraints.
 *
 * @author Marcus Pinnecke
 */
public final class FeatureUtils {

	public static final ConcreteFeatureFilter CONCRETE_FEATURE_FILTER = new ConcreteFeatureFilter();

	public static final HiddenFeatureFilter HIDDEN_FEATURE_FILTER = new HiddenFeatureFilter();

	public static final Function<IFeature, String> GET_OLD_FEATURE_NAME =
		feature -> feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName());

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

		return Functional.map(list, IFeatureStructure::getFeature);
	}

	public static List<IFeature> convertToFeatureList(List<IFeatureStructure> list) {
		requireNonNull(list);

		return Functional.toList(Functional.map(list, IFeatureStructure::getFeature));
	}

	public static List<IFeatureStructure> convertToFeatureStructureList(List<IFeature> list) {
		requireNonNull(list);

		return Functional.toList(Functional.map(list, IFeature::getStructure));
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

	public static Iterable<IFeature> extractHiddenFeatures(final IFeatureModel model) {
		requireNonNull(model);

		return extractHiddenFeatures(model.getFeatures());
	}

	/**
	 * Extracts all concrete features from an object that yields features. Basically, an invocation of this method on <b>features</b> will return an iterable
	 * object that yields a feature <i>f</i> from <b>features</b> if and only if <i>f</i> is concrete. Since the implementation based on iterators, it is a lazy
	 * filtering without modification of <b>features</b>.
	 *
	 * <br> <br> The extraction is done via {@link de.ovgu.featureide.fm.core.functional.Functional#filter(Iterable, Predicate)}
	 *
	 * @since 3.0
	 * @param features An iterable object providing features
	 * @author Marcus Pinnecke
	 * @return An iterable object that yields all concrete features of <b>features</b>
	 */
	public static Iterable<IFeature> extractConcreteFeatures(final Iterable<IFeature> features) {
		requireNonNull(features);

		return Functional.filter(features, CONCRETE_FEATURE_FILTER);
	}

	public static Iterable<IFeature> extractHiddenFeatures(final Iterable<IFeature> features) {
		requireNonNull(features);

		return Functional.filter(features, HIDDEN_FEATURE_FILTER);
	}

	/**
	 * Extracts all concrete features from a feature model as a list of strings by calling {@link Functional#mapToStringList(Iterable)} on the result of
	 * {@link #extractConcreteFeatures(IFeatureModel)} using <code>model.getFeatures()</code>.
	 *
	 * @since 3.0
	 * @param model A feature model
	 * @author Marcus Pinnecke
	 * @return A list of strings that contains the feature names of all concrete features of <b>features</b>
	 */
	public static List<String> extractConcreteFeaturesAsStringList(IFeatureModel model) {
		requireNonNull(model);

		return new ArrayList<>(Functional.mapToStringList(FeatureUtils.extractConcreteFeatures(model.getFeatures())));
	}

	public static Iterable<String> extractFeatureNames(Iterable<IFeature> features) {
		requireNonNull(features);

		return Functional.map(features, IFeature::getName);
	}

	public static Iterable<String> extractOldFeatureNames(Iterable<IFeature> features) {
		requireNonNull(features);

		return Functional.map(features, GET_OLD_FEATURE_NAME);
	}

	public static final FeatureModelAnalyzer getAnalyser(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return FeatureModelManager.getAnalyzer(featureModel);
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

		return Functional.map(feature.getStructure().getChildren(), IFeatureStructure::getFeature);
	}

	public static final int getChildrenCount(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().getChildrenCount();
	}

	public static final List<String> getComments(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(featureModel.getProperty().getComments());
	}

	public static final Iterable<String> getConcreteFeatureNames(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return FeatureUtils.extractConcreteFeaturesAsStringList(featureModel);
	}

	public static final Collection<IFeature> getConcreteFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(FeatureUtils.extractConcreteFeatures(featureModel));
	}

	public static final Collection<IFeature> getHiddenFeatures(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(FeatureUtils.extractHiddenFeatures(featureModel));
	}

	public static final Node getConstraint(IFeatureModel featureModel, int index) {
		requireNonNull(featureModel);

		return Functional.toList(getPropositionalNodes(featureModel)).get(index);
	}

	@Deprecated
	public static final ConstraintAttribute getConstraintAttribute(IConstraint constraint) {
		requireNonNull(constraint);

		return ConstraintAttribute.NORMAL;
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

	public static final Collection<IFeature> getDeadFeatures(IConstraint constraint, IFeatureModel fm, Collection<IFeature> fmDeadFeatures) {
		requireNonNull(constraint);
		requireNonNull(fmDeadFeatures);

		Collection<IFeature> deadFeaturesBefore = null;
		final Node propNode = constraint.getNode();
		if (propNode != null) {
			fm.removeConstraint(constraint);
			deadFeaturesBefore = FeatureModelManager.getAnalyzer(fm).getDeadFeatures(null);
			fm.addConstraint(new Constraint(fm, propNode));
			fm.handleModelDataChanged();
		}

		final Collection<IFeature> deadFeaturesAfter = new LinkedList<>();
		for (final IFeature f : fmDeadFeatures) {
			final IFeature feature = fm.getFeature(f.getName());
			// XXX why can the given feature not be found?
			if ((feature != null) && !deadFeaturesBefore.contains(feature)) {
				deadFeaturesAfter.add(f);
			}
		}
		return deadFeaturesAfter;
	}

	public static final String getDescription(IFeature feature) {
		requireNonNull(feature);

		return feature.getProperty().getDescription();
	}

	public static final IFeature getFeature(IFeatureModel featureModel, CharSequence name) {
		requireNonNull(featureModel);
		requireNonNull(name);

		return featureModel.getFeature(name.toString());
	}

	/**
	 * @param featureModel A feature model
	 * @param featureName The name of a feature
	 * @return True iff the given feature model contains a feature with the given name
	 */
	public static final boolean containsFeature(IFeatureModel featureModel, CharSequence featureName) {
		requireNonNull(featureModel);
		requireNonNull(featureName);

		return featureModel.getFeature(featureName) != null;
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

	public static final Set<String> getOldFeatureNames(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toSet(FeatureUtils.extractOldFeatureNames(featureModel.getFeatures()));
	}

	public static final List<String> getOldFeatureNamesList(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return Functional.toList(FeatureUtils.extractOldFeatureNames(featureModel.getFeatures()));
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

	public static final Map<String, IFeature> getFeatureTable(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getFeatureTable();
	}

	public static final IFeature getFirstChild(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().getFirstChild().getFeature();
	}

	public static final IFeature getLastChild(IFeature feature) {
		requireNonNull(feature);

		return feature.getStructure().getLastChild().getFeature();
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

		return Functional.mapToList(featureModel.getConstraints(), IConstraint::getNode);
	}

	public static List<Node> getPropositionalNodes(Iterable<IConstraint> constraints) {
		requireNonNull(constraints);

		return Functional.toList(Functional.map(constraints, IConstraint::getNode));
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

	/**
	 * Returns the root features of the given model, primarily used for models with multiple root features.
	 *
	 * @param featureModel The feature model
	 * @return The root feature of the given model if it is not implicit, or its children otherwise.
	 */
	public static final List<IFeature> getRoots(IFeatureModel featureModel) {
		final IFeatureStructure root = featureModel.getStructure().getRoot();
		if (root.getFeature().getProperty().isImplicit()) {
			return root.getChildren().stream().map(IFeatureStructure::getFeature).collect(Collectors.toList());
		} else {
			return Arrays.asList(root.getFeature());
		}
	}

	public static final void handleModelDataChanged(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		featureModel.handleModelDataChanged();
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

	/**
	 * Recursively calculates the depth of the subtree starting from this feature using DFS. If this feature has no children, the depth is 0.
	 *
	 * @return The depth of the subtree starting from this feature
	 */
	public static final int getSubtreeDepth(IFeature feature) {
		if (!hasChildren(feature)) {
			return 0;
		}
		int max = -1;
		for (final IFeature f : getChildren(feature)) {
			final int current = getSubtreeDepth(f);
			if (current > max) {
				max = current;
			}
		}
		return max + 1;
	}

	public static final boolean hasConcrete(IFeatureModel featureModel) {
		requireNonNull(featureModel);

		return featureModel.getStructure().hasConcrete();
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

		return feature.getStructure().isAncestor(next.getStructure());
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
		// TODO check unnecessary null checks, may cause defect itself
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

		feature.getStructure().setChildren(Functional.toList(Functional.map(children, IFeature::getStructure)));
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
		final Collection<IFeature> foFeatures = FeatureModelManager.getAnalyzer(clonedModel).getFalseOptionalFeatures(null);
		for (final IFeature feature : FeatureModelManager.getAnalyzer(featureModel).getFalseOptionalFeatures(null)) {
			if (!foFeatures.contains(clonedModel.getFeature(feature.getName())) && !falseOptionalFeatures.contains(feature)) {
				falseOptionalFeatures.add(feature);
				found = true;
			}
		}
		return found;
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

	/**
	 * Makes sure that a feature name is unique by appending a number
	 *
	 * @param featureModel feature mode that the new feature name will be inserted into
	 * @param prefix chosen feature name
	 * @return chosen feature name with a number attached to it
	 */
	public static String getFeatureName(final IFeatureModel featureModel, String prefix) {
		final Set<String> existingFeatureNames = FeatureUtils.getFeatureNames(featureModel);
		int number = 1;
		if (!existingFeatureNames.contains(prefix)) {
			return prefix;
		}
		while (existingFeatureNames.contains(prefix + ++number)) {}
		return prefix + number;
	}
}
