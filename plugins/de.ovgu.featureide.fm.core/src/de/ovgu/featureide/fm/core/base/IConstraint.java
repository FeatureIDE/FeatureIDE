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

import java.util.Collection;

import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.base.impl.AConstraint;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * The <code>IConstraint</code> interface represents any class which acts in the sense of a <i>Constraint</i> in FeatureIDE. <br/> <br/> A constraint is a
 * propositional formula on {@link IFeature features} inside a {@link IFeatureModel feature model} which gives further conditions a valid configuration must
 * satisfy. A constraint allows conditions statements which are not directly expressibly using the {@link de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor}
 * since feature models are typically modeled in a hierarchy here. <br/> <br/> A constraint can affect a set of features depending on the conditions given by
 * both the feature model and other constraints. For instance, a constraint can lead to a condition on features which is constant (un-)satisfied, or forces an
 * optional group of features to be mandatory. These affects can be analyzed such that it is known whenever a given constraint result in such effects (see
 * {@link ConstraintAttribute}). <br/> <br/> For ease of use, FeatureIDE provides an adapter for this interface, {@link AConstraint} which can be used as a
 * starting point for custom implementations. In a broader sense, constraints in FeatureIDE also satisfy the {@link IFeatureModelElement} element which deals
 * with identification of constraints and models. <br/> <br/> Instances of <code>IConstraint</code> are intended to be instantiated by a
 * {@link IFeatureModelFactory}. <br/> <br/> <b>Example</b> <br/> The following example shows the instantiation of a <code>IConstraint</code> instance using
 * FeatureIDE's default {@link FeatureModel} and {@link Constraint} implementation over the standard factories. The constraint created give the condition, that
 * a feature <code>A</code> implies another feature <code>B</code>. <code> <pre> IFeatureModel model = FMFactoryManager.getFactory().createFeatureModel();
 * IConstraint c = FMFactoryManager.getFactory().createConstraint(model, new Implies(new Literal("A"), new Literal("B"))); </pre> </code>
 *
 * @see de.ovgu.featureide.fm.core.base.impl.AConstraint Default implementation of <code>IConstraint</code> (as starting point for custom implementations)
 *
 * @see IFeature Interface for feature constraints (<code>IFeature</code>)
 * @see IFeatureModel Interface for feature models (<code>IFeatureModel</code>)
 * @see IFeatureProperty Interface for feature properties (<code>IFeatureProperty</code>)
 * @see IFeatureStructure Interface for a feature's structure (<code>IFeatureStructure</code>)
 *
 * @see de.ovgu.featureide.fm.core.base.impl.AFeatureModelElement Feature model element default implementation (<code>IFeatureModelElement</code>
 *      implementation)
 * @see de.ovgu.featureide.fm.core.base.impl.AFeature Default implementation for features (<code>AFeature</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureModel Default implementation for feature models (<code>FeatureModel</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureProperty Default implementation for feature properties (<code>FeatureProperty</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureStructure Default implementation for a feature's structure (<code>FeatureStructure</code>)
 *
 * @since 3.0
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public interface IConstraint extends IFeatureModelElement {

	/**
	 * Constructs a new instance of <code>IConstraint</code> equal to this constraint but with a new reference. <br/> <br/> A new constraint equal to this is
	 * created. Optional, the <code>feature model</code> can be changed. More in detail a new constraint <code>c'</code> is constructed based on this constraint
	 * <code>c</code> such that at least <ul> <li><code>c</code> underlying {@link org.prop4j.Node node} <code>n</code> containing the propositional formula is
	 * accessible by <code>c'</code>. A deep copy of <code>n</code> is not required.</li> <li>the flag indicating a selection of this constraint in the UI
	 * (e.g., {@link de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor}) is equal for <code>c</code> and <code>c'</code></li> <li>if <code>c</code> inherits
	 * {@link IFeatureModelElement}, <code>c'</code> must deep copy the required members of this implementation</li> </ul> It holds <code>c' != c</code> and
	 * <code>c.equals(c')</code>. <br/> <br/> <b>Note:</b> the parameter <b>newFeatureModel</b> is intended to change the feature model context of the newly
	 * created, and affects members if this constraint implements {@link IFeatureModelElement}. <br/><br/> <b>Notes on side effects and <code>null</code>
	 * references</b><br/> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b> in this object.</li> <li>does <b>not</b> affect the
	 * <b>parameter</b> <code>newFeatureModel</code>.</li> <li>the parameter <code>newFeature</code> is expected to be <b>non-null</b></li> <li>the returned
	 * <b>result</b> is guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 *
	 * @param newFeatureModel a possible new context for this constraint
	 *
	 * @see AConstraint Default implementation for constraints (extending implementation for <code>IFeatureModelElement</code>
	 * @see IFeatureModelElement Feature model element interface
	 *
	 * @since 3.0
	 *
	 * @return a new instance of this constraint which has a new reference
	 */
	IConstraint clone(IFeatureModel newFeatureModel);

	/**
	 * Returns analysis results for this constraint, i.e., how this constraint affects the feature model. <br/> <br/> A constraint can affect a set of features
	 * depending on the conditions given by both the feature model and other constraints. For instance, a constraint can lead to a condition on features which
	 * is constant (un-)satisfied, or forces an optional group of features to be mandatory. These affects can be analyzed such that it is known whenever a given
	 * constraint result in such effects (see {@link ConstraintAttribute}). <br/> <br/> The result of a former analysis is intended to be stored in the
	 * constraint, such that this methods returns the affects of this constraint to the model. Possible affects by this constraint are: <ul>
	 * <li>{@link de.ovgu.featureide.fm.core.ConstraintAttribute#DEAD leads to dead features}</li>
	 * <li>{@link de.ovgu.featureide.fm.core.ConstraintAttribute#FALSE_OPTIONAL leads to false optional features}</li>
	 * <li>{@link de.ovgu.featureide.fm.core.ConstraintAttribute#NORMAL do not affect the model in a special way}</li>
	 * <li>{@link de.ovgu.featureide.fm.core.ConstraintAttribute#REDUNDANT is redundant, i.e., the condition by this constraint is already covered elsewhere}
	 * </li> <li>{@link de.ovgu.featureide.fm.core.ConstraintAttribute#TAUTOLOGY leads to a tautology expression}</li>
	 * <li>{@link de.ovgu.featureide.fm.core.ConstraintAttribute#UNSATISFIABLE leads to unsatisfiable expressions}</li>
	 * <li>{@link de.ovgu.featureide.fm.core.ConstraintAttribute#VOID_MODEL voids the feature model}</li> </ul>
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b> in
	 * this object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 * @see ConstraintAttribute constraint attributes
	 *
	 * @since 3.0
	 *
	 * @return A value which indicates how the constraints affects the feature model
	 */
	ConstraintAttribute getConstraintAttribute();

	/**
	 * Returns the collection of features contained in the underlying formula of this constraint. <br/> <br/> A constraint contains one or more features. In the
	 * default implementation, the propositional formula is constructed via nodes of a satisfiability solver (see {@link Node}). This method returns a view on
	 * these items. <br/> <br/> <b>Note</b>: The returned collection is intended to be cached. If the cache is empty, {@link IConstraint#setContainedFeatures()}
	 * is called automatically. The return collection might be out-dated until a new call to {@link IConstraint#setContainedFeatures()} is done manually.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>affects</b> the <b>members</b> in
	 * this object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 * @since 3.0
	 *
	 * @see #setContainedFeatures()
	 *
	 * @return a collections of features which are part of the propositional formula of this constraint
	 */
	Collection<IFeature> getContainedFeatures();

	/**
	 * Returns the parameter of the last {@link #setDeadFeatures(Iterable)} call, or <code>null</code> if no such call happens before invoking this method.
	 * <br/> <br/> <b>Note</b>: The dead feature collection is <u>not</u> calculated when calling this method. Therefore, a call to
	 * {@link #setDeadFeatures(Iterable)} is required plus eventually a call to {@link #getDeadFeatures(SatSolver, IFeatureModel, Collection)}. <br/> <br/>
	 * <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b> in this
	 * object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and <b>unmodifiable</b></li> </ul>
	 *
	 * @see #setDeadFeatures(Iterable)
	 * @see #getDeadFeatures(SatSolver, IFeatureModel, Collection)
	 *
	 *
	 *
	 * @since 3.0
	 *
	 * @return A collection of features which are marked as dead features.
	 */
	Collection<IFeature> getDeadFeatures();

	/**
	 * Calculates and returns a iterable collection of features which are marked as <i>dead</i> due to the affect of this constraint to the feature model
	 * <code>featureModel</code>. The calculation whenever a constraint leads to <i>dead</i> features is done over the instance of a {@link SatSolver
	 * satisfaction solver} given by the parameter <code>solver</code>. From the calculated set of dead features in <code>featureModel</code>, the features
	 * contained in <code>excludeFeatures</code> are excluded before the collection of dead features is return, i.e., features in <code>excludeFeatures</code>
	 * are not contained in the resulting collection even if they might be <i>dead</i>. <br/> <br/> <b>Node on duplicate elements</b>: The calculated collection
	 * of <i>dead</i> features have not to contain duplicates.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b> in
	 * this object.</li> <li>might <b>affect</b> cache entries in the <b>parameter</b> <code>newFeatureModel</code>.</li> <li>does <b>not</b> affect the
	 * <b>parameter</b> <code>execludeFeatures</code>.</li> <li>the parameter are assumed to be <b>non-null</b></li> <li>the returned <b>result</b> is
	 * guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 * @since 3.0
	 *
	 * @param solver a satisfaction solver
	 * @param featureModel the feature model for which the affect of this constraint should be analyzed in terms of <i>dead</i> feature affect.
	 * @param exlcudeFeatuers a collection features which should be removed from the resulting collection of <i>dead</i> features before this collection is
	 *        returned.
	 * @return An iterable over <i>dead</i> features in <code>featureModel</code> caused by this constraint, which are not included in the
	 *         <code>excludeFeatures</code> collection.
	 */
	Collection<IFeature> getDeadFeatures(SatSolver solver, IFeatureModel featureModel, Collection<IFeature> exlcudeFeatuers);

	/**
	 * Returns the parameter of the last {@link #setFalseOptionalFeatures(IFeatureModel, Collection)} call, or <code>null</code> if no such call happens before
	 * invoking this method. <br/> <br/> <b>Note</b>: The false optional feature collection is <u>not</u> calculated when calling this method. Therefore, a call
	 * to {@link #setFalseOptionalFeatures(IFeatureModel, Collection)} is required. <br/> <br/> <b>Notes on side effects and <code>null</code>
	 * references</b><br/> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b> in this object.</li> <li>the returned <b>result</b> is
	 * guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 *
	 * @see #setDeadFeatures(Iterable)
	 * @see #getDeadFeatures(SatSolver, IFeatureModel, Collection)
	 *
	 * @since 3.0
	 *
	 * @return A collection of features which are marked as dead features.
	 */
	Collection<IFeature> getFalseOptional();

	/**
	 * @since 3.0
	 *
	 *        <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>not</b> affect the
	 *        <b>members</b> in this object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 * @return The underlying propositional formula node
	 */
	Node getNode();

	/**
	 * Overwrites the underlying propositional formula <code>node</code> for this constraint.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>affects</b> <b>members</b> in this
	 * object.</li> <li>the parameter <code>node</code> is expected to be <b>non-null</b></li> </ul>
	 *
	 * @since 3.0
	 *
	 * @param node propositional node
	 */
	void setNode(Node node);

	/**
	 * Returns whenever this constraints contains features which are marked as <i>hidden</i> <br/> <br/> Checks if one or more features contained in this
	 * feature is marked as <i>hidden</i> by checking if one feature in the set of contained features is <i>hidden</i> or, if the parent of one feature in the
	 * set of contained features is <i>hidden</i>. If such a feature is found, the method returns <b>true</b>, otherwise <b>false</b>.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b> in
	 * this object.</li> </ul>
	 *
	 * @since 3.0
	 *
	 * @return <b>true</b> if a feature (or a features parent) is marked as <i>hidden</i> and contained in the formula of this constraint
	 */
	boolean hasHiddenFeatures();

	/**
	 * Sets the analysis attribute for this constraints which determine how this constraint affects features. <br/><br/> A constraint can affect a set of
	 * features depending on the conditions given by both the feature model and other constraints. For instance, a constraint can lead to a condition on
	 * features which is constant (un-)satisfied, or forces an optional group of features to be mandatory. These affects can be analyzed such that it is known
	 * whenever a given constraint result in such effects (see {@link ConstraintAttribute}). <br/><br/>
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>affect</b> the <b>members</b> in this
	 * object.</li> <li>does <b>not</b> affect the <b>parameters</b>.</li> <li>the parameters are expected to be <b>non-null</b></li> </ul>
	 *
	 * @since 3.0
	 *
	 * @param attribute The affect caused by this constraint
	 * @param notifyListeners A flag indicating if listeners should be notified about this change
	 */
	void setConstraintAttribute(ConstraintAttribute attribute, boolean notifyListeners);

	/**
	 * Calculates and caches the collection of contained features in this constraint.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>affect</b> the <b>members</b> in this
	 * object.</li> </ul>
	 *
	 * @see #getContainedFeatures()
	 *
	 * @since 3.0
	 */
	void setContainedFeatures();

	/**
	 * Sets the collection of <i>dead</i> features caused by this constraint to the values stored in <code>deadFeature</code>.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>affect</b> the <b>members</b> in this
	 * object.</li> <li>does <b>not</b> affect the <b>parameter</b> <code>deadFeatures</code>.</li> <li>the parameter <code>deadFeatures</code> is expected to
	 * be <b>non-null</b></li> </ul>
	 *
	 * @see #getDeadFeatures()
	 * @see Functional#getEmptyIterable(Class) Setting an empty iterable
	 *
	 * @param deadFeatures iterable of features which are claimed to be dead
	 */
	void setDeadFeatures(Iterable<IFeature> deadFeatures);

	/**
	 * Calculates and sets the collections of <i>false optional</i> features in <code>featureModel</code> caused by this constraint. <br/> <br/> The set of
	 * <i>false optional</i> features is updated to the current state, and accessible by calling {@link #getFalseOptional()}. The method returns <b>true</b> if
	 * this set is empty, and <b>false</b> otherwise. <br/> <br/> <b>Note</b>: The collection <code>collection</code> is modified such that newly calculated
	 * <i>false optional</i> features are removed from <code>collection</code> (if any). Therefore, {@link #getFalseOptional()} returns the entire set of
	 * <i>false optional</i> features while <code>collection</code> contains elements (as provided before calling this method) minus the content of
	 * {@link #getFalseOptional()}.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>affect</b> the <b>members</b> in this
	 * object.</li> <li>does <b>affect</b> the <b>parameter</b> <code>collection</code>.</li> <li>the parameters are expected to be <b>non-null</b></li> </ul>
	 *
	 * @since 3.0
	 *
	 * @param featureModel The context which is affected by this constraint
	 * @param collection A set containing features. Elements in <code>collection</code> are removed, if they are marked as <i>false optional</i> during this
	 *        method call.
	 * @return <b>true</b> if this constraint affects a least one feature to be <i>false optional</i>, <b>false</b> otherwise.
	 */
	boolean setFalseOptionalFeatures(IFeatureModel featureModel, Collection<IFeature> collection);

	/**
	 * String representation of the constraint's propositional formula. <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling
	 * this method: <ul> <li>does <b>not</b> affect the <b>members</b> in this object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and
	 * <b>modifiable</b></li> </ul>
	 *
	 * @return String representation of the constraint's propositional formula.
	 */
	String getDisplayName();

	/**
	 * Sets the collection of <i>false-optional</i> features caused by this constraint to the values stored in <code>falseOptionalFeatures</code>.
	 *
	 * <br/><br/> <b>Notes on side effects and <code>null</code> references</b><br/> Calling this method: <ul> <li>does <b>affect</b> the <b>members</b> in this
	 * object.</li> <li>does <b>not</b> affect the <b>parameter</b> <code>foFeatures</code>.</li> <li>the parameter <code>foFeatures</code> is expected to be
	 * <b>non-null</b></li> </ul>
	 *
	 * @see #getFalseOptional()
	 * @see Functional#getEmptyIterable(Class) Setting an empty iterable
	 *
	 * @param foFeatures iterable of features which are claimed to be falseOptional
	 */
	void setFalseOptionalFeatures(Iterable<IFeature> foFeatures);

	/**
	 * Set the description
	 * @param description
	 */
	void setDescription(String description);
	
	/**
	 * Returns the description
	 * @return
	 */
	String getDescription();

}


