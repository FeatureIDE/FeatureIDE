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

import java.util.Collection;

import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.base.impl.AConstraint;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;

/**
 * The <code>IConstraint</code> interface represents any class which acts in the sense of a <i>Constraint</i> in FeatureIDE.
 * <br/>
 * <br/>
 * A constraint is a propositional formula on {@link IFeature features} inside a {@link IFeatureModel feature model} which
 * gives further conditions a valid configuration must satisfy. A constraint allows conditions statements which are
 * not directly expressibly using the {@link de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor} since 
 * feature models are typically modeled in a hierarchy here. 
 * <br/>
 * <br/> 
 * A constraint can affect a set of features depending on the conditions given by both the feature model and other
 * constraints. For instance, a constraint can lead to a condition on features which is constant (un-)satisfied,
 * or forces an optional group of features to be mandatory. These affects can be analyzed such that it is 
 * known whenever a given constraint result in such effects (see @link {@link ConstraintAttribute}).
 * <br/>
 * <br/>
 * For ease of use, FeatureIDE provides an adapter for this interface, {@link AConstraint} which can be used
 * as a starting point for custom implementations.
 * <br/>
 * <br/>
 * Instances of <code>IConstraint</code> are intended to be instantiated by a {@link IFeatureModelFactory}. 
 * <br/>
 * <br/>
 * <b>Example</b>
 * <br/>
 * The following example shows the instantiation of a <code>IConstraint</code> instance using FeatureIDE's
 * default {@link FeatureModel} and {@link Constraint} implementation over the standard factories. The constraint
 * created give the condition, that a feature <code>A</code> implies another feature <code>B</code>.
 * <code>
 * <pre>
 * IFeatureModel model = FMFactoryManager.getFactory().createFeatureModel();
 * IConstraint c = FMFactoryManager.getFactory().createConstraint(model, new Implies(new Literal("A"), new Literal("B")));
 * </pre>
 * </code>  
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public interface IConstraint extends IFeatureModelElement {

	IConstraint clone(IFeatureModel newFeatureModel);

	ConstraintAttribute getConstraintAttribute();

	Collection<IFeature> getContainedFeatures();

	Collection<IFeature> getDeadFeatures();

	Iterable<IFeature> getDeadFeatures(SatSolver solver, IFeatureModel fm, Collection<IFeature> fmDeadFeatures);

	Collection<IFeature> getFalseOptional();

	Node getNode();
	
	void setNode(Node node);

	boolean hasHiddenFeatures();

	void setConstraintAttribute(ConstraintAttribute attri, boolean fire);

	void setContainedFeatures();

	void setDeadFeatures(Iterable<IFeature> deadFeatures);

	boolean setFalseOptionalFeatures(IFeatureModel clone, Collection<IFeature> fmFalseOptionals);
	
	String getDisplayName();

}
