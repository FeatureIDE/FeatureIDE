/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.annotation.CheckForNull;

import org.eclipse.core.runtime.IProgressMonitor;
import org.prop4j.And;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * A collection of methods for working with {@link FeatureModel} will replace
 * the corresponding methods in {@link FeatureModel}
 * 
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class FeatureModelAnalyzer {
	
	private static final String TRUE = "True";

	private static final String FALSE = "False";

	private final Collection<Feature> cachedDeadFeatures = new LinkedList<Feature>();
	
	private final Collection<Feature> chachedFalseOptionalFeatures = new LinkedList<Feature>();
	
	private boolean cachedValidity = true;
	
	private FeatureModel fm;
	
	/**
	 * Defines whether features should be included into calculations.
	 * If features are not analyzed, then constraints a also NOT analyzed.
	 */
	public boolean calculateFeatures = true;
	/**
	 * Defines whether constraints should be included into calculations.
	 */
	public boolean calculateConstraints = true;
	/**
	 * Defines whether redundant constraints should be calculated.
	 */
	public boolean calculateRedundantConstraints = true;
	/**
	 * Defines whether constraints that are tautologies should be calculated.
	 */
	public boolean calculateTautologyConstraints = true;
	/**
	 * Defines whether analysis should be performed automatically.
	 */
	public boolean runCalculationAutomatically = true;

	/**
	 * A flag indicating that the calculation should be canceled.
	 */
	private boolean cancel = false;

	@CheckForNull
	private IProgressMonitor monitor;

	private FeatureDependencies dependencies;
	
	public Collection<Feature> getCachedFalseOptionalFeatures() {
		return chachedFalseOptionalFeatures;
	}

	/**
	 * Returns the value calculated during the last call of
	 * updateFeatureModel().
	 * 
	 * @return cached value
	 */
	public boolean valid() {
		return cachedValidity;
	}
	
	protected FeatureModelAnalyzer(FeatureModel fm) {
		this.fm = fm;
	}

	/**
	 * Returns the feature dependencies of the feature model. 
	 * If the has model changed call {@link FeatureModelAnalyzer#setDependencies()} to calculate 
	 * current dependencies.
	 * @return
	 */
	public FeatureDependencies getDependencies() {
		if (dependencies == null) {
			dependencies = new FeatureDependencies(fm);
		}
		return dependencies;
	}
	
	/**
	 * Calculates new dependencies.
	 * @return
	 */
	public void setDependencies() {
		dependencies = new FeatureDependencies(fm);
	}

	public boolean isValid() throws TimeoutException {
		Node root = NodeCreator.createNodes(fm.clone());
		return new SatSolver(root, 1000).isSatisfiable();
	}

	/**
	 * checks whether A implies B for the current feature model.
	 * 
	 * in detail the following condition should be checked whether
	 * 
	 * FM => ((A1 and A2 and ... and An) => (B1 or B2 or ... or Bn))
	 * 
	 * is true for all values
	 * 
	 * @param A
	 *            set of features that form a conjunction
	 * @param B
	 *            set of features that form a conjunction
	 * @return
	 * @throws TimeoutException
	 */
	public boolean checkImplies(Collection<Feature> a, Collection<Feature> b)
			throws TimeoutException {
		if (b.isEmpty())
			return true;

		Node featureModel = NodeCreator.createNodes(fm.clone());

		// B1 or B2 or ... Bn
		Node condition = disjunct(b);
		// (A1 and ... An) => (B1 or ... Bn)
		if (!a.isEmpty())
			condition = new Implies(conjunct(a), condition);
		// FM => (A => B)
		Implies finalFormula = new Implies(featureModel, condition);
		return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
	}
	
	public boolean checkIfFeatureCombinationNotPossible(Feature a, Collection<Feature> b) throws TimeoutException {
		if (b.isEmpty())
			return true;

		Node featureModel = NodeCreator.createNodes(fm.clone());
		boolean notValid = true;
		for (Feature f : b) {
			Node node = new And(new And(featureModel, new Literal(NodeCreator.getVariable(f, fm.clone()))),  
					new Literal(NodeCreator.getVariable(a, fm.clone())));
			notValid &= !new SatSolver(node, 1000).isSatisfiable();
		}
		return notValid;
	}
	
	
	/**
	 * checks some condition against the feature model. use only if you know
	 * what you are doing!
	 * 
	 * @return
	 * @throws TimeoutException
	 */
	public boolean checkCondition(Node condition) {

		Node featureModel = NodeCreator.createNodes(fm);
		// FM => (condition)
		Implies finalFormula = new Implies(featureModel, condition.clone());
		try {
			return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
			return false;
		}
	}

	/**
	 * Checks whether the given featureSets are mutually exclusive in the given
	 * context and for the current feature model.
	 * 
	 * In detail it is checked whether FM => (context => (at most one of the
	 * featureSets are present)) is a tautology.
	 * 
	 * Here is an example for a truth table of
	 * "at most one the featureSets are present" for three feature sets A, B and
	 * C:
	 * 
	 * A B C result ------------------------ T T T F T T F F T F T F T F F T F T
	 * T F F T F T F F T T F F F T
	 * 
	 * If you want to check XOR(featureSet_1, ..., featureSet_n) you can call
	 * areMutualExclusive() && !mayBeMissing().
	 * 
	 * @param context
	 *            context in which everything is checked
	 * @param featureSets
	 *            list of feature sets that are checked to be mutually exclusive
	 *            in the given context and for the current feature model
	 * 
	 * @return true, if the feature sets are mutually exclusive || false,
	 *         otherwise
	 * @throws TimeoutException
	 */
	public boolean areMutualExclusive(Collection<Feature> context,
			Collection<Set<Feature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || (featureSets.size() < 2))
			return true;

		Node featureModel = NodeCreator.createNodes(fm);

		ArrayList<Node> conjunctions = new ArrayList<Node>(featureSets.size());
		for (Collection<Feature> features : featureSets) {
			if ((features != null) && !features.isEmpty())
				conjunctions.add(conjunct(features));
			else
				// If one feature set is empty (i.e. the code-fragment is always
				// present) than it cannot be
				// mutually exclusive to the other ones.
				return false;
		}

		// We build the conjunctive normal form of the formula to check
		Collection<Object> forOr = new LinkedList<Object>();
		Collection<Object> allNot = new LinkedList<Object>();
		for (int i = 0; i < conjunctions.size(); ++i) {
			allNot.add(new Not(conjunctions.get(i).clone()));

			Collection<Object> forAnd = new LinkedList<Object>();
			for (int j = 0; j < conjunctions.size(); ++j) {
				if (j == i)
					forAnd.add(conjunctions.get(j).clone());
				else
					forAnd.add(new Not(conjunctions.get(j).clone()));
			}
			forOr.add(new And(forAnd));
		}
		forOr.add(new And(allNot));

		Node condition = new Or(forOr);
		if ((context != null) && !context.isEmpty())
			condition = new Implies(conjunct(context), condition);

		Implies finalFormula = new Implies(featureModel, condition);
		return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
	}

	/**
	 * Checks whether there exists a set of features that is valid within the
	 * feature model and the given context, so that none of the given feature
	 * sets are present, i.e. evaluate to true.
	 * 
	 * In detail it is checked whether there exists a set F of features so that
	 * eval(FM, F) AND eval(context, F) AND NOT(eval(featureSet_1, F)) AND ...
	 * AND NOT(eval(featureSet_n, F)) is true.
	 * 
	 * If you want to check XOR(featureSet_1, ..., featureSet_n) you can call
	 * areMutualExclusive() && !mayBeMissing().
	 * 
	 * @param context
	 *            context in which everything is checked
	 * @param featureSets
	 *            list of feature sets
	 * 
	 * @return true, if there exists such a set of features, i.e. if the
	 *         code-fragment may be missing || false, otherwise
	 * @throws TimeoutException
	 */
	public boolean mayBeMissing(Collection<Feature> context,
			Collection<Set<Feature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || featureSets.isEmpty())
			return false;

		Node featureModel = NodeCreator.createNodes(fm);
		Collection<Object> forAnd = new LinkedList<Object>();

		for (Collection<Feature> features : featureSets) {
			if ((features != null) && !features.isEmpty())
				forAnd.add(new Not(conjunct(features)));
			else
				return false;
		}

		Node condition = new And(forAnd);
		if ((context != null) && !context.isEmpty())
			condition = new And(conjunct(context), condition);

		Node finalFormula = new And(featureModel, condition);
		return new SatSolver(finalFormula, 1000).isSatisfiable();
	}

	/**
	 * Checks whether there exists a set of features that is valid within the
	 * feature model, so that all given features are present.
	 * 
	 * In detail it is checked whether there exists a set F of features so that
	 * eval(FM, F) AND eval(feature_1, F) AND eval(feature_n, F) is true.
	 * 
	 * @param features
	 * 
	 * @return true if there exists such a set of features || false, otherwise
	 * @throws TimeoutException
	 */
	public boolean exists(Collection<Feature> features) throws TimeoutException {
		if ((features == null) || (features.isEmpty()))
			return true;

		Node featureModel = NodeCreator.createNodes(fm);
		Node finalFormula = new And(featureModel, conjunct(features));
		return new SatSolver(finalFormula, 1000).isSatisfiable();
	}

	public Node conjunct(Collection<Feature> b) {
		Iterator<Feature> iterator = b.iterator();
		Node result = new Literal(NodeCreator.getVariable(iterator.next(), fm));
		while (iterator.hasNext())
			result = new And(result, new Literal(NodeCreator.getVariable(
					iterator.next(), fm)));

		return result;
	}
	
	public Node disjunct(Collection<Feature> b) {
		Iterator<Feature> iterator = b.iterator();
		Node result = new Literal(NodeCreator.getVariable(iterator.next(), fm));
		while (iterator.hasNext())
			result = new Or(result, new Literal(NodeCreator.getVariable(
					iterator.next(), fm)));

		return result;
	}	

	/**
	 * Returns the list of features that occur in all variants, where one of the
	 * given features is selected. If the given list of features is empty, this
	 * method will calculate the features that are present in all variants
	 * specified by the feature model.
	 * 
	 * @param timeout
	 *            in milliseconds
	 * @param selectedFeatures
	 *            a list of feature names for which
	 * @return a list of features that is common to all variants
	 */
	public Collection<String> commonFeatures(long timeout,
			Object... selectedFeatures) {
		Node formula = NodeCreator.createNodes(fm);
		if (selectedFeatures.length > 0)
			formula = new And(formula, new Or(selectedFeatures));
		SatSolver solver = new SatSolver(formula, timeout);
		Collection<String> common = new LinkedList<String>();
		for (Literal literal : solver.knownValues())
			if (literal.positive)
				common.add(literal.var.toString());
		return common;
	}

	public Collection<Feature> getDeadFeatures() {
		return getDeadFeatures(1000);	
	}

	/**
	 * Adds the propNode to the solver to calculate dead features.
	 */
	public Collection<Feature> getDeadFeatures(SatSolver solver, Node propNode) {
		solver.addClauses(propNode.clone().toCNF());
		Collection<Feature> deadFeatures = new LinkedList<Feature>();
		for (Literal e : solver.knownValues()) {
			String var = e.var.toString();
			if (!e.positive && !FALSE.equals(var) && !TRUE.equals(var)) {
				Feature feature = fm.getFeature(var);
				if (feature != null) {
					deadFeatures.add(feature);
				}
			}
		}
		cachedDeadFeatures.clear();
		cachedDeadFeatures.addAll(deadFeatures);
		return deadFeatures;
	}
	
	public Collection<Feature> getDeadFeatures(int timeout) {
		// cloning the FM, because otherwise the resulting formula is wrong if
		// renamed features are involved
		// TODO: Check other calls of createNodes
		Node root = NodeCreator.createNodes(fm.clone());
		Collection<Feature> deadFeatures = new LinkedList<Feature>();
		for (Literal e : new SatSolver(root, timeout).knownValues()) {
			String var = e.var.toString();
			if (!e.positive && !FALSE.equals(var) && !TRUE.equals(var)) {
				Feature feature = fm.getFeature(var);
				if (feature != null) {
					deadFeatures.add(feature);
				}
			}
		}
		cachedDeadFeatures.clear();
		cachedDeadFeatures.addAll(deadFeatures);
		return deadFeatures;
	}
	
	public Collection<Feature> getCoreFeatures() {
		// cloning the FM, because otherwise the resulting formula is wrong if
		// renamed features are involved
		// TODO: Check other calls of createNodes
		Node root = NodeCreator.createNodes(fm.clone());
		Collection<Feature> coreFeatures = new LinkedList<Feature>();
		for (Literal e : new SatSolver(root, 1000).knownValues()) {
			String var = e.var.toString();
			if (e.positive && !FALSE.equals(var) && !TRUE.equals(var)) {
				Feature feature = fm.getFeature(var);
				if (feature != null) {
					coreFeatures.add(feature);
				}
			}
		}
		return coreFeatures;
	}
	
	/**
	 * @param monitor 
	 * @return Hashmap: key entry is Feature/Constraint, value usually
	 *         indicating the kind of attribute
	 */
	/*
	 * check all changes of this method and called methods with the related tests and
	 * benchmarks, see fm.core-test plug-in
	 * think about performance (no unnecessary or redundant calculations)
	 * 
	 * Hashing might be fast for locating features, but creating a HashSet is costly 
	 * So LinkedLists are much faster because the number of feature in the set is usually small (e.g. dead features)
	 */
	public HashMap<Object, Object> analyzeFeatureModel(IProgressMonitor monitor) {
		this.monitor = monitor;
		if (calculateConstraints) {
			beginTask(fm.getConstraintCount() + 2);
		} else {
			beginTask(2);
		}
		HashMap<Object, Object> oldAttributes = new HashMap<Object, Object>();
		HashMap<Object, Object> changedAttributes = new HashMap<Object, Object>();

		// put root always in so it will be refreshed (void/non-void)
		changedAttributes.put(fm.getRoot(), FeatureStatus.NORMAL);
		if (calculateFeatures) {
			updateFeatures(oldAttributes, changedAttributes);
		}
		if (!canceled() && calculateConstraints) {
			updateConstraints(oldAttributes, changedAttributes);
		}
		// put root always in so it will be refreshed (void/non-void)
//		changedAttributes.put(fm.getRoot(), ConstraintAttribute.VOID_MODEL);
		return changedAttributes;
	}

	private void beginTask(int totalWork) {
		if (monitor != null) {
			monitor.beginTask("Analyze", totalWork);
		}
	}

	public void updateConstraints(HashMap<Object, Object> oldAttributes,
			HashMap<Object, Object> changedAttributes) {
		FeatureModel clone = fm.clone();
		clone.constraints.clear();
		SatSolver solver = new SatSolver(NodeCreator.createNodes(clone), 1000);
	
		Collection<Feature> fmDeadFeatures = getCachedDeadFeatures();
		Collection<Feature> fmFalseOptionals = getCachedFalseOptionalFeatures();
		try {
			if (!cachedValidity) { 
				// case: invalid model
				boolean contraintFound = false;
				for (Constraint constraint : fm.getConstraints()) {
					if (canceled()) {
						return;
					}
					
					clone.addConstraint(constraint);
					try {
						if (!contraintFound && !clone.getAnalyser().isValid()) {
							if (oldAttributes.get(constraint) != ConstraintAttribute.VOID_MODEL) {
								changedAttributes.put(constraint,
										ConstraintAttribute.VOID_MODEL);
							}
							contraintFound = true;
							constraint.setConstraintAttribute(
									ConstraintAttribute.VOID_MODEL, false);
						}
					} catch (TimeoutException e) {
						FMCorePlugin.getDefault().logError(e);
					}
					// contradiction?
					SatSolver satsolverUS = new SatSolver(constraint.getNode().clone(), 1000);
					try {
						if (!satsolverUS.isSatisfiable()) {
							if (oldAttributes.get(constraint) != ConstraintAttribute.UNSATISFIABLE) {
								changedAttributes.put(constraint, ConstraintAttribute.UNSATISFIABLE);
							}
							constraint.setConstraintAttribute(
									ConstraintAttribute.UNSATISFIABLE, false);
						}
					} catch (TimeoutException e) {
						FMCorePlugin.getDefault().logError(e);
					}

				}
				if (monitor != null) {
					monitor.done();
				}
				return;
			}
			
			// Default case
			/**
			 * Algorithm description:
			 * Start from a model without constraints;
			 * Add one constraint after another;
			 * Add the NEW introduces errors/warnings to the constraint;
			 */
			if (calculateRedundantConstraints || calculateTautologyConstraints) {
				setSubTask("Find redundant constraints");
				/** Remove redundant constraints for further analysis **/
				for (Constraint constraint : fm.getConstraints()) {
					if (canceled()) {
						return;
					}
					if (calculateTautologyConstraints) {
						// tautology
						SatSolver satsolverTAU = new SatSolver(new Not(constraint.getNode().clone()), 1000);
						try {
							if (!satsolverTAU.isSatisfiable()) {
								if (oldAttributes.get(constraint) != ConstraintAttribute.TAUTOLOGY) {
									changedAttributes.put(constraint, ConstraintAttribute.TAUTOLOGY);
								}
								constraint.setConstraintAttribute(ConstraintAttribute.TAUTOLOGY, false);
								worked(1);
								continue;
							}
						} catch (TimeoutException e) {
							FMCorePlugin.getDefault().logError(e);
						}
					}
					
					if (calculateRedundantConstraints) {
						findRedundantConstraints(clone, constraint, changedAttributes, oldAttributes);
						if (changedAttributes.containsKey(constraint)) {						
							worked(1);
						}	
					}
					
				}
				clone = fm.clone();
				clone.constraints.clear();
			}
			/** Look for dead and false optional features **/
			for (Constraint constraint : fm.getConstraints()) {
				if (canceled()) {
					return;
				}
				
				if (changedAttributes.get(constraint) == ConstraintAttribute.TAUTOLOGY) {
					continue;
				}
				if (changedAttributes.get(constraint) == ConstraintAttribute.REDUNDANT) {
					continue;
				}
				
				constraint.setContainedFeatures();
				if (fmFalseOptionals.isEmpty() && fmDeadFeatures.isEmpty()) {
					constraint.getDeadFeatures().clear();
					constraint.getFalseOptional().clear();
					continue;
				}
				
				worked(1);
				setSubTask(constraint.toString());
				clone.addConstraint(constraint);
				oldAttributes.put(constraint, constraint.getConstraintAttribute());
				constraint.setContainedFeatures();
				
				// if the constraint leads to false optional features it is added to
				// changedAttributes in order to refresh graphics later
				if (fmFalseOptionals.isEmpty()) {
					constraint.getFalseOptional().clear();
				} else if (constraint.setFalseOptionalFeatures(clone, fmFalseOptionals)) {
					constraint.setConstraintAttribute(ConstraintAttribute.FALSE_OPTIONAL, false);
					changedAttributes.put(constraint, ConstraintAttribute.FALSE_OPTIONAL);
				}
				
				if (!fmDeadFeatures.isEmpty()) {
					Collection<Feature> deadFeatures = constraint.getDeadFeatures(solver, clone, fmDeadFeatures);
					if (!deadFeatures.isEmpty()) {
						constraint.setDeadFeatures(deadFeatures);
						constraint.setConstraintAttribute(ConstraintAttribute.DEAD, false);
						changedAttributes.put(constraint, ConstraintAttribute.DEAD);
					}
				} else {
					constraint.getDeadFeatures().clear();
				}
				if (!changedAttributes.containsKey(constraint)) {
					constraint.setConstraintAttribute(ConstraintAttribute.NORMAL, false);
					changedAttributes.put(constraint, ConstraintAttribute.NORMAL);
				}

			}
		} catch (ConcurrentModificationException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	private boolean canceled() {
		return cancel || (monitor != null ? monitor.isCanceled() : false);
	}

	private void worked(int workDone) {
		if (monitor != null) {
			monitor.worked(workDone);
		}
	}
	
	private void setSubTask(String name) {
		if (monitor != null) {
			monitor.subTask(name);
		}
	}

	private void findRedundantConstraints(FeatureModel clone, Constraint constraint, Map<Object, Object> changedAttributes, Map<Object,Object> oldAttributes) {
		FeatureModel oldModel = clone.clone();
		clone.addConstraint(constraint);
		ModelComparator comparator = new ModelComparator(500);
		Comparison comparison = comparator.compare(clone, oldModel);
		if (comparison == Comparison.REFACTORING) {
			if (oldAttributes.get(constraint) != ConstraintAttribute.REDUNDANT) {
				changedAttributes.put(constraint, ConstraintAttribute.REDUNDANT);
			}
			constraint.setConstraintAttribute(ConstraintAttribute.REDUNDANT, false);
		}
	}

	public void updateFeatures(Map<Object, Object> oldAttributes,
			Map<Object, Object> changedAttributes) {
		setSubTask("Analyze features.");
		for (Feature bone : fm.getFeatures()) {
			oldAttributes.put(bone, bone.getFeatureStatus());
			
			if (bone.getFeatureStatus() != FeatureStatus.NORMAL) {
				changedAttributes.put(bone, FeatureStatus.FALSE_OPTIONAL);
			}
			bone.setFeatureStatus(FeatureStatus.NORMAL, false);
			bone.setRelevantConstraints();
		}

		try {
			cachedValidity = isValid();
		} catch (TimeoutException e) {
			cachedValidity = true;
			FMCorePlugin.getDefault().logError(e);
		}

		try {
			if (canceled()) {
				return;
			}
			/**
			 * here the saved dead features at the feature model are calculated and set
			 */
			setSubTask("Get Dead Features.");
			cachedDeadFeatures.clear();
			
			for (Feature deadFeature : getDeadFeatures()) {
				if (oldAttributes.get(deadFeature) != FeatureStatus.DEAD) {
					changedAttributes.put(deadFeature, FeatureStatus.DEAD);
				}
				cachedDeadFeatures.add(deadFeature);
				deadFeature.setFeatureStatus(FeatureStatus.DEAD, false);
			}
			worked(1);
			if (canceled()) {
				return;
			}
			
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}

		try {
			if (cachedValidity) {
				setSubTask("Get False Optional Features.");
				getFalseOptionalFeature(oldAttributes, changedAttributes);
				worked(1);
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		calculateHidden(changedAttributes);
	}

	/**
	 * Calculations for indeterminate hidden features
	 * @param changedAttributes
	 */
	public void calculateHidden(Map<Object, Object> changedAttributes) {
		if (!fm.hasHidden()) {
			return;
		}			
		setSubTask("calculate indetrminate hidden features");
		/**
		 * First every relevant constraint of every hidden feature is checked if its form equals 
		 * "hidden feature" <=> A
		 * where A is an expression containing only non hidden features
		 * If there is a constraint of that kind for a hidden feature it is added to a list. 
		 */
		Collection<Feature> list = new LinkedList<Feature>();
		Collection<Feature> hiddenFeatures = getHiddenFeatures();
		for (Feature feature : hiddenFeatures) {	
			for (Constraint constraint : feature.getRelevantConstraints()) {
				Node node = constraint.getNode();
				if (node instanceof Equals) {
					Node[] children = node.getChildren();
					Node leftChild = children[0];
					Node rightChild = children[1];
					if (leftChild instanceof Literal && ((Literal) leftChild).var.equals(feature.getName())) {
						Constraint	rightConstraint = new Constraint(fm, rightChild);
						rightConstraint.setContainedFeatures();
						if (!rightConstraint.hasHiddenFeatures()) {
							list.add(feature);
							break;
						}
					}
					if (rightChild instanceof Literal &&  ((Literal) rightChild).var.equals(feature.getName())) {
						Constraint  leftConstraint = new Constraint(fm, leftChild);
						leftConstraint.setContainedFeatures();
						if (!leftConstraint.hasHiddenFeatures()) {
							list.add(feature);
							break;
						}
					}
				}
			}
		}
		
		/**
		 * Additionally each Node is checked if the atomic set containing it, consists of indeterminate hidden nodes only.
		 * If this is the case it's also indeterminate.
		 * A node is therefore not marked indeterminate if it either
		 *  - has a non-hidden Node in its atomic set defining its state or
		 *  - if a Node of its atomic set is determined by a constraint of the above form.
		 */
		FeatureDependencies featureDependencies = new FeatureDependencies(fm, false);
		beginTask(fm.getConstraintCount() + hiddenFeatures.size());
		for (Feature feature: hiddenFeatures) {
			if (canceled()) {
				return;
			}
			setSubTask("calculate indetrminate hidden features for " + feature.getName());
			if (!list.contains(feature)) {
				Collection<Feature> set = featureDependencies.getImpliedFeatures(feature);
				boolean noHidden = false;
				for (Feature f : set) {
					if (!f.isHidden() && !f.hasHiddenParent() || list.contains(f)) {
						if (featureDependencies.isAlways(f, feature)) {
							noHidden = true; 
							break;
						}
					}
				}	

				if (!noHidden) {
					changedAttributes.put(feature, FeatureStatus.INDETERMINATE_HIDDEN);					
					feature.setFeatureStatus(FeatureStatus.INDETERMINATE_HIDDEN, false);
				}
				
				worked(1);
			}
		}
	}
	
	/**
	 * Gets all hidden features their children
	 * @return
	 */
	public Collection<Feature> getHiddenFeatures() {
		Collection<Feature> hiddenFeatures = new LinkedList<Feature>();
		for (Feature f : fm.getFeatures()) {
			if (f.isHidden() || f.hasHiddenParent()) {
				hiddenFeatures.add(f);
			}
		}
		return hiddenFeatures;
	}

	private void getFalseOptionalFeature(Map<Object, Object> oldAttributes,
			Map<Object, Object> changedAttributes) {
		chachedFalseOptionalFeatures.clear();
		for (Feature f : getFalseOptionalFeatures()) {
			changedAttributes.put(f,FeatureStatus.FALSE_OPTIONAL);
			f.setFeatureStatus(FeatureStatus.FALSE_OPTIONAL, false);
			chachedFalseOptionalFeatures.add(f);
		}
	}
	
	public Collection<Feature> getFalseOptionalFeatures() {
		Collection<Feature> falseOptionalFeatures = new LinkedList<Feature>();
		for (Feature feature : fm.getFeatures()) {
			try {
				if (!feature.isMandatory() && !feature.isRoot()) {
					SatSolver satsolver = new SatSolver(new Not(new Implies(
							new And(new Literal(feature.getParent().getName()),
									NodeCreator.createNodes(fm.clone())),
							new Literal(feature.getName()))), 1000);
					if (!satsolver.isSatisfiable()) {
						falseOptionalFeatures.add(feature);
					}
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
		return falseOptionalFeatures;
	}
	
	public Collection<Feature> getFalseOptionalFeatures(Collection<Feature> fmFalseOptionals) {
		Collection<Feature> falseOptionalFeatures = new LinkedList<Feature>();
		for (Feature feature : fmFalseOptionals) {
			try {
				if (!feature.isMandatory() && !feature.isRoot()) {
					SatSolver satsolver = new SatSolver(new Not(new Implies(
							new And(new Literal(feature.getParent().getName()),
									NodeCreator.createNodes(fm.clone())),
							new Literal(feature.getName()))), 1000);
					if (!satsolver.isSatisfiable()) {
						falseOptionalFeatures.add(feature);
					}
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
		return falseOptionalFeatures;
	}

	public int countConcreteFeatures() {
		int number = 0;
		for (Feature feature : fm.getFeatures())
			if (feature.isConcrete())
				number++;
		return number;
	}

	public int countHiddenFeatures() {
		int number = 0;
		for (Feature feature : fm.getFeatures()) {
			if (feature.isHidden() || feature.hasHiddenParent()) {
				number++;
			}
		}
		return number;
	}

	public int countTerminalFeatures() {
		int number = 0;
		for (Feature feature : fm.getFeatures())
			if (!feature.hasChildren())
				number++;
		return number;
	}
	
	/**
	 * Sets the cancel status of analysis.<br>
	 * <code>true</code> if analysis should be stopped.
	 */
	public void cancel(boolean value) {
		cancel = value;
	}

	public Collection<Feature> getCachedDeadFeatures() {
		return cachedDeadFeatures;
	}
}
