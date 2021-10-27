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

import java.util.Collection;
import java.util.Set;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.base.impl.AConstraint;
import de.ovgu.featureide.fm.core.base.impl.Constraint;

/**
 * The <code>IConstraint</code> interface represents any class which acts in the sense of a <i>Constraint</i> in FeatureIDE. <br> <br> A constraint is a
 * propositional formula on {@link IFeature features} inside a {@link IFeatureModel feature model} which gives further conditions a valid configuration must
 * satisfy. A constraint allows conditions statements which are not directly expressibly using the FeatureDiagramEditor since feature models are typically
 * modeled in a hierarchy here. <br> <br> A constraint can affect a set of features depending on the conditions given by both the feature model and other
 * constraints. For instance, a constraint can lead to a condition on features which is constant (un-)satisfied, or forces an optional group of features to be
 * mandatory. These affects can be analyzed such that it is known whenever a given constraint result in such effects (see {@link ConstraintAttribute}). <br>
 * <br> For ease of use, FeatureIDE provides an adapter for this interface, {@link AConstraint} which can be used as a starting point for custom
 * implementations. In a broader sense, constraints in FeatureIDE also satisfy the {@link IFeatureModelElement} element which deals with identification of
 * constraints and models. <br> <br> Instances of <code>IConstraint</code> are intended to be instantiated by a {@link IFeatureModelFactory}. <br> <br>
 * <b>Example</b> <br> The following example shows the instantiation of a <code>IConstraint</code> instance using FeatureIDE's default {@link IFeatureModel} and
 * {@link Constraint} implementation over the standard factories. The constraint created give the condition, that a feature <code>A</code> implies another
 * feature <code>B</code>. <code> IFeatureModel model = FMFactoryManager.getFactory().createFeatureModel(); IConstraint c =
 * FMFactoryManager.getFactory().createConstraint(model, new Implies(new Literal("A"), new Literal("B"))); </code>
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
	 * Constructs a new instance of <code>IConstraint</code> equal to this constraint but with a new reference. <br> <br> A new constraint equal to this is
	 * created. Optional, the <code>feature model</code> can be changed. More in detail a new constraint <code>c'</code> is constructed based on this constraint
	 * <code>c</code> such that at least <ul> <li><code>c</code> underlying {@link org.prop4j.Node node} <code>n</code> containing the propositional formula is
	 * accessible by <code>c'</code>. A deep copy of <code>n</code> is not required.</li> <li>the flag indicating a selection of this constraint in the UI
	 * (e.g., FeatureDiagramEditor) is equal for <code>c</code> and <code>c'</code></li> <li>if <code>c</code> inherits {@link IFeatureModelElement},
	 * <code>c'</code> must deep copy the required members of this implementation</li> </ul> It holds <code>c' != c</code> and <code>c.equals(c')</code>. <br>
	 * <br> <b>Note:</b> the parameter <b>newFeatureModel</b> is intended to change the feature model context of the newly created, and affects members if this
	 * constraint implements {@link IFeatureModelElement}. <br><br> <b>Notes on side effects and <code>null</code> references</b><br> Calling this method: <ul>
	 * <li>does <b>not</b> affect the <b>members</b> in this object.</li> <li>does <b>not</b> affect the <b>parameter</b> <code>newFeatureModel</code>.</li>
	 * <li>the parameter <code>newFeature</code> is expected to be <b>non-null</b></li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and
	 * <b>modifiable</b></li> </ul>
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
	 * Returns the collection of features contained in the underlying formula of this constraint. <br> <br> A constraint contains one or more features. In the
	 * default implementation, the propositional formula is constructed via nodes of a satisfiability solver (see {@link Node}). This method returns a view on
	 * these items. <br> <br> <b>Note</b>: The returned collection is intended to be cached.
	 *
	 * <br><br> <b>Notes on side effects and <code>null</code> references</b><br> Calling this method: <ul> <li>does <b>affects</b> the <b>members</b> in this
	 * object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 * @since 3.0
	 *
	 * @return a collections of features which are part of the propositional formula of this constraint
	 */
	Collection<IFeature> getContainedFeatures();

	/**
	 * @since 3.0
	 *
	 *        <br><br> <b>Notes on side effects and <code>null</code> references</b><br> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b>
	 *        in this object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and <b>modifiable</b></li> </ul>
	 *
	 * @return The underlying propositional formula node
	 */
	Node getNode();

	/**
	 * Overwrites the underlying propositional formula <code>node</code> for this constraint.
	 *
	 * <br><br> <b>Notes on side effects and <code>null</code> references</b><br> Calling this method: <ul> <li>does <b>affects</b> <b>members</b> in this
	 * object.</li> <li>the parameter <code>node</code> is expected to be <b>non-null</b></li> </ul>
	 *
	 * @since 3.0
	 *
	 * @param node propositional node
	 */
	void setNode(Node node);

	/**
	 * Returns whenever this constraints contains features which are marked as <i>hidden</i> <br> <br> Checks if one or more features contained in this feature
	 * is marked as <i>hidden</i> by checking if one feature in the set of contained features is <i>hidden</i> or, if the parent of one feature in the set of
	 * contained features is <i>hidden</i>. If such a feature is found, the method returns <b>true</b>, otherwise <b>false</b>.
	 *
	 * <br><br> <b>Notes on side effects and <code>null</code> references</b><br> Calling this method: <ul> <li>does <b>not</b> affect the <b>members</b> in
	 * this object.</li> </ul>
	 *
	 * @since 3.0
	 *
	 * @return <b>true</b> if a feature (or a features parent) is marked as <i>hidden</i> and contained in the formula of this constraint
	 */
	boolean hasHiddenFeatures();

	/**
	 * String representation of the constraint's propositional formula. <br><br> <b>Notes on side effects and <code>null</code> references</b><br> Calling this
	 * method: <ul> <li>does <b>not</b> affect the <b>members</b> in this object.</li> <li>the returned <b>result</b> is guaranteed <b>non-null</b> and
	 * <b>modifiable</b></li> </ul>
	 *
	 * @return String representation of the constraint's propositional formula.
	 */
	String getDisplayName();

	/**
	 * Set the description
	 *
	 * @param description
	 */
	void setDescription(String description);

	/**
	 * Returns the description
	 *
	 * @return the description
	 */
	String getDescription();

	/**
	 * Returns the set of tags this constraint has. Tags can be used to group multiple constraints.
	 *
	 * @return {@link Collection}
	 */
	Set<String> getTags();

	/**
	 * Sets the set of tags.
	 *
	 * @param tags - {@link Collection}
	 */
	void setTags(Set<String> tags);

}
