/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.functional.Functional.map;
import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZE;
import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZE_FEATURES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_INDETRMINATE_HIDDEN_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_INDETRMINATE_HIDDEN_FEATURES_FOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.FIND_REDUNDANT_CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_DEAD_FEATURES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.GET_FALSE_OPTIONAL_FEATURES_;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
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
import org.sat4j.specs.IConstr;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;
/**
 * A collection of methods for working with {@link IFeatureModel} will replace
 * the corresponding methods in {@link IFeatureModel}
 * 
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelAnalyzer {

	public static enum Attribute {
		Mandatory, Optional, Alternative, Or, Abstract, 
		Concrete, Hidden, Dead, FalseOptional, 
		IndetHidden, UnsatisfiableConst, TautologyConst, 
		VoidModelConst, RedundantConst
	}
	

	private final boolean[] attributeFlags = new boolean[Attribute.values().length];
	
	private static final String TRUE = "True";

	private static final String FALSE = "False";

	private List<IFeature> cachedDeadFeatures = Collections.emptyList();
	private List<IFeature> cachedCoreFeatures = Collections.emptyList();
	
	private final Collection<IFeature> chachedFalseOptionalFeatures = new LinkedList<>();
	
	private boolean cachedValidity = true;
	
	private IFeatureModel fm;
	
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
	
	public Collection<IFeature> getCachedFalseOptionalFeatures() {
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
	
	public FeatureModelAnalyzer(IFeatureModel fm) {
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
		return new SatSolver(AdvancedNodeCreator.createCNF(fm), 1000, false).isSatisfiable();
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
	public boolean checkImplies(Collection<IFeature> a, Collection<IFeature> b)
			throws TimeoutException {
		if (b.isEmpty())
			return true;

		Node featureModel = NodeCreator.createNodes(fm.clone(null));

		// B1 or B2 or ... Bn
		Node condition = disjunct(b);
		// (A1 and ... An) => (B1 or ... Bn)
		if (!a.isEmpty())
			condition = new Implies(conjunct(a), condition);
		// FM => (A => B)
		Implies finalFormula = new Implies(featureModel, condition);
		return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
	}
	
	public boolean checkIfFeatureCombinationNotPossible(IFeature a, Collection<IFeature> b) throws TimeoutException {
		if (b.isEmpty())
			return true;

		Node featureModel = NodeCreator.createNodes(fm.clone(null));
		boolean notValid = true;
		for (IFeature f : b) {
			Node node = new And(new And(featureModel, new Literal(NodeCreator.getVariable(f, fm.clone(null)))),  
					new Literal(NodeCreator.getVariable(a, fm.clone(null))));
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
		Node featureModel = AdvancedNodeCreator.createNodes(fm);
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
	 * AT_MOST_ONE_THE_FEATURESETS_ARE_PRESENT for three feature sets A, B and
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
	public boolean areMutualExclusive(Collection<IFeature> context,
			Collection<Set<IFeature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || (featureSets.size() < 2))
			return true;

		Node featureModel = AdvancedNodeCreator.createNodes(fm);

		ArrayList<Node> conjunctions = new ArrayList<Node>(featureSets.size());
		for (Collection<IFeature> features : featureSets) {
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
	public boolean mayBeMissing(Collection<IFeature> context,
			Collection<Set<IFeature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || featureSets.isEmpty())
			return false;

		Node featureModel = NodeCreator.createNodes(fm);
		Collection<Object> forAnd = new LinkedList<Object>();

		for (Collection<IFeature> features : featureSets) {
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
	public boolean exists(Collection<IFeature> features) throws TimeoutException {
		if ((features == null) || (features.isEmpty()))
			return true;

		Node featureModel = NodeCreator.createNodes(fm);
		Node finalFormula = new And(featureModel, conjunct(features));
		return new SatSolver(finalFormula, 1000).isSatisfiable();
	}

	public Node conjunct(final Collection<IFeature> b) {
		return new And(new And(Functional.toList(map(b, new IFunction<IFeature, Literal>() {

			@Override
			public Literal invoke(IFeature t) {
				return new Literal(NodeCreator.getVariable(t, fm));
			}

		}))), fm);
	}
	
	
	public Node disjunct(Collection<IFeature> b) {
		Iterator<IFeature> iterator = b.iterator();
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
	public Collection<String> commonFeatures(long timeout, Object... selectedFeatures) {
		Node formula = NodeCreator.createNodes(fm);
		if (selectedFeatures.length > 0) {
			formula = new And(formula, new Or(selectedFeatures));
		}
		final Collection<String> common = new ArrayList<>();
		final SatSolver solver = new SatSolver(formula, timeout);
		for (Literal literal : solver.knownValues(SatSolver.ValueType.TRUE)) {
			common.add(literal.var.toString());
		}
		return common;
	}

	/**
	 * Adds the propNode to the solver to calculate dead features.
	 */
	public List<IFeature> getDeadFeatures(SatSolver solver, Node propNode) {
		solver.addClauses(propNode.clone().toCNF());
		final ArrayList<IFeature> deadFeatures = new ArrayList<>();
		deadFeatures.clear();
		
		for (Literal e : solver.knownValues(SatSolver.ValueType.FALSE)) {
			final String var = e.var.toString();
			if (!FALSE.equals(var) && !TRUE.equals(var)) {
				final IFeature feature = fm.getFeature(var);
				if (feature != null) {
					deadFeatures.add(feature);
				}
			}
		}
		
		cachedDeadFeatures = deadFeatures;
		return getCachedDeadFeatures();
	}
	
	public List<IFeature> getCoreFeatures() {
		return getCoreFeatures(1000);	
	}
	
	public List<IFeature> getDeadFeatures() {
		return getDeadFeatures(1000);	
	}

	public List<List<IFeature>> analyzeFeatures() {
		return analyzeFeatures(1000);
	}
	
	public List<IFeature> getCoreFeatures(long timeout, Object... selectedFeatures) {
		return analyzeFeatures(timeout, SatSolver.ValueType.TRUE, selectedFeatures).get(0);
	}
	
	public List<IFeature> getDeadFeatures(long timeout, Object... selectedFeatures) {
		return analyzeFeatures(timeout, SatSolver.ValueType.FALSE, selectedFeatures).get(1);
	}

	public List<List<IFeature>> analyzeFeatures(long timeout, Object... selectedFeatures) {
		return analyzeFeatures(timeout, SatSolver.ValueType.ALL, selectedFeatures);
	}
	
	private List<List<IFeature>> analyzeFeatures(long timeout, SatSolver.ValueType vt, Object... selectedFeatures) {
		final ArrayList<IFeature> coreFeatures = new ArrayList<>();
		final ArrayList<IFeature> deadFeatures = new ArrayList<>();
		
		Node formula = AdvancedNodeCreator.createCNF(fm);
		if (selectedFeatures.length > 0) {
			final Node[] extendedChildren = Arrays.copyOf(formula.getChildren(), formula.getChildren().length + 1);
			extendedChildren[formula.getChildren().length] = new Or(selectedFeatures);
			formula.setChildren(extendedChildren);
		}
		final SatSolver solver = new SatSolver(formula, timeout, false);

		for (Literal literal : solver.knownValues(vt)) {
			final String var = literal.var.toString();
			if (!FALSE.equals(var) && !TRUE.equals(var)) {
				final IFeature feature = fm.getFeature(var);
				if (feature != null) {
					if (literal.positive) {
						coreFeatures.add(feature);
					} else {
						deadFeatures.add(feature);
					}
				}
			}
		}

		cachedCoreFeatures = coreFeatures;
		cachedDeadFeatures = deadFeatures;

		final ArrayList<List<IFeature>> result = new ArrayList<>(2);
		result.add(getCachedCoreFeatures());
		result.add(getCachedDeadFeatures());
		
		return result;
	}
	
	public List<List<IFeature>> getAtomicSets() {
		final ArrayList<List<IFeature>> result = new ArrayList<>();
		
		final SatSolver solver = new SatSolver(AdvancedNodeCreator.createCNF(fm), 1000, false);
		
		for (List<Literal> literalList : solver.atomicSets()) {
			final List<IFeature> setList = new ArrayList<>();
			result.add(setList);
			for (Literal literal : literalList) {
				final String var = literal.var.toString();
				if (!FALSE.equals(var) && !TRUE.equals(var)) {
					final IFeature feature = fm.getFeature(var);
					if (feature != null) {
						setList.add(feature);
					}
				}
			}
			
		}
		return result;
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
		resetAttributeFlags();
		this.monitor = monitor;
		if (calculateConstraints) {
			beginTask(fm.getConstraintCount() + 2);
		} else {
			beginTask(2);
		}
		HashMap<Object, Object> oldAttributes = new HashMap<Object, Object>();
		HashMap<Object, Object> changedAttributes = new HashMap<Object, Object>();

		// put root always in so it will be refreshed (void/non-void)
		changedAttributes.put(fm.getStructure().getRoot().getFeature(), FeatureStatus.NORMAL);
		if (calculateFeatures) {
			updateFeatures(oldAttributes, changedAttributes);
		}
		if (!canceled() && calculateConstraints) {
			updateConstraints(oldAttributes, changedAttributes);
		}
		// put root always in so it will be refreshed (void/non-void)
		return changedAttributes;
	}

	private void beginTask(int totalWork) {
		if (monitor != null) {
			monitor.beginTask(ANALYZE, totalWork);
		}
	}

	public void updateConstraints(HashMap<Object, Object> oldAttributes,
			HashMap<Object, Object> changedAttributes) {
		IFeatureModel clone = fm.clone(null);
		clone.setConstraints(new LinkedList<IConstraint>());
		SatSolver solver = new SatSolver(NodeCreator.createNodes(clone), 1000);
	
		Collection<IFeature> fmDeadFeatures = new ArrayList<>(getCachedDeadFeatures());
		Collection<IFeature> fmFalseOptionals = getCachedFalseOptionalFeatures();
		try {
			final List<IConstraint> constraints = fm.getConstraints();
			if (!cachedValidity) { 
				// case: invalid model
				boolean contraintFound = false;
				for (IConstraint constraint : constraints) {
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

			clone.setConstraints(new LinkedList<IConstraint>());
			
			// Default case
			/**
			 * Algorithm description:
			 * Start from a model without constraints;
			 * Add one constraint after another;
			 * Add the NEW introduces errors/warnings to the constraint;
			 */
			if (calculateRedundantConstraints || calculateTautologyConstraints) {
				setSubTask(FIND_REDUNDANT_CONSTRAINTS);
				
				final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(clone);
				nodeCreator.setCnfType(CNFType.Regular);
				nodeCreator.setIncludeBooleanValues(true);
				nodeCreator.setModelType(ModelType.OnlyStructure);
				final SatSolver redundantSat = new SatSolver(nodeCreator.createNodes(), 1000);
				redundantSat.setDBSimplificationAllowed(false);
				
				final List<List<IConstr>> constraintMarkers = new ArrayList<>();
				for (IConstraint constraint : constraints) {
					constraintMarkers.add(redundantSat.addTempConstraint(constraint.getNode().toCNF()));
				}
				redundantSat.isSatisfiable();
				
				/** Remove redundant constraints for further analysis **/
				int i = -1;
				for (IConstraint constraint : constraints) {
					i++;
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
						boolean atLeastOneRemoved = false;
						for (IConstr cm : constraintMarkers.get(i)) {
							if (cm != null) {
								atLeastOneRemoved = true;
								redundantSat.removeConstraint(cm);
							}
						}
						if (atLeastOneRemoved) {
							clone.addConstraint(constraint);
							findRedundantConstraints(redundantSat, constraint, changedAttributes, oldAttributes);
						} else {
							setConstraintAttribute(constraint, changedAttributes, oldAttributes, ConstraintAttribute.REDUNDANT);
						}
						if (changedAttributes.containsKey(constraint)) {						
							worked(1);
						}
					}
					
				}
				clone = fm.clone(null);
				clone.setConstraints(new LinkedList<IConstraint>());
			}
			/** Look for dead and false optional features **/
			for (IConstraint constraint : constraints) {
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
					if (constraint.getConstraintAttribute() != ConstraintAttribute.NORMAL) {
						constraint.setConstraintAttribute(ConstraintAttribute.NORMAL, false);
						changedAttributes.put(constraint, ConstraintAttribute.NORMAL);
					}
					constraint.setDeadFeatures(Functional.getEmptyIterable(IFeature.class));
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
					Collection<IFeature> deadFeatures = Functional.toList(constraint.getDeadFeatures(solver, clone, fmDeadFeatures));
					if (!deadFeatures.isEmpty()) {
						fmDeadFeatures.removeAll(deadFeatures);
						constraint.setDeadFeatures(deadFeatures);
						constraint.setConstraintAttribute(ConstraintAttribute.DEAD, false);
						changedAttributes.put(constraint, ConstraintAttribute.DEAD);
					}
				} else {
					constraint.setDeadFeatures(Collections.<IFeature>emptyList());
				}
				if (!changedAttributes.containsKey(constraint)) {
					constraint.setConstraintAttribute(ConstraintAttribute.NORMAL, false);
					changedAttributes.put(constraint, ConstraintAttribute.NORMAL);
				}

			}
		} catch (TimeoutException | ConcurrentModificationException e) {
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

	private void findRedundantConstraints(SatSolver sat, IConstraint constraint, Map<Object, Object> changedAttributes, Map<Object,Object> oldAttributes) {			
		final Node constraintNode = constraint.getNode().toCNF();
		
		boolean redundant = true;
		if (constraintNode instanceof And) {
			final Node[] clauses = constraintNode.getChildren();
			for (int i = 0; i < clauses.length; i++) {
				if (!sat.isImplied(clauses[i].getChildren())) {
					redundant = false;
					break;
				}
			}
		} else if (constraintNode instanceof Or) {
			redundant = sat.isImplied(constraintNode.getChildren());
		} else {
			redundant = sat.isImplied((Literal) constraintNode);
		}
		
		if (redundant) {
			setConstraintAttribute(constraint, changedAttributes, oldAttributes, ConstraintAttribute.REDUNDANT);
		} else {
			sat.addClauses(constraintNode);
		}
	}

	private void setConstraintAttribute(IConstraint constraint, Map<Object, Object> changedAttributes, Map<Object, Object> oldAttributes, ConstraintAttribute constraintAttribute) {
		if (oldAttributes.get(constraint) != constraintAttribute) {
			changedAttributes.put(constraint, constraintAttribute);
		}
		constraint.setConstraintAttribute(constraintAttribute, false);
	}

	public void updateFeatures(Map<Object, Object> oldAttributes,
			Map<Object, Object> changedAttributes) {
		setSubTask(ANALYZE_FEATURES_);
		for (IFeature bone : fm.getFeatures()) {
			oldAttributes.put(bone, bone.getProperty().getFeatureStatus());
			
			if (bone.getProperty().getFeatureStatus() != FeatureStatus.NORMAL) {
				changedAttributes.put(bone, FeatureStatus.FALSE_OPTIONAL);
			}
			bone.getProperty().setFeatureStatus(FeatureStatus.NORMAL, false);
			FeatureUtils.setRelevantConstraints(bone);
		}

		try {
			cachedValidity = isValid();
		} catch (TimeoutException e) {
			cachedValidity = true;
			FMCorePlugin.getDefault().logError(e);
		}
		
		try {
			if (cachedValidity) {
				setSubTask(GET_FALSE_OPTIONAL_FEATURES_);
				getFalseOptionalFeature(oldAttributes, changedAttributes);
				worked(1);
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		
		try {
			if (canceled()) {
				return;
			}
			/**
			 * here the saved dead features at the feature model are calculated and set
			 */
			setSubTask(GET_DEAD_FEATURES_);
			for (IFeature deadFeature : getDeadFeatures()) {
				if (oldAttributes.get(deadFeature) != FeatureStatus.DEAD) {
					changedAttributes.put(deadFeature, FeatureStatus.DEAD);
				}
				deadFeature.getProperty().setFeatureStatus(FeatureStatus.DEAD, false);
			}
			worked(1);
			if (canceled()) {
				return;
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
		if (!fm.getStructure().hasHidden()) {
			return;
		}			
		setSubTask(CALCULATE_INDETRMINATE_HIDDEN_FEATURES);
		/**
		 * First every relevant constraint of every hidden feature is checked if its form equals 
		 * HIDDEN_FEATURE <=> A
		 * where A is an expression containing only non hidden features
		 * If there is a constraint of that kind for a hidden feature it is added to a list. 
		 */
		Collection<IFeature> list = new LinkedList<IFeature>();
		Collection<IFeature> hiddenFeatures = getHiddenFeatures();
		for (IFeature feature : hiddenFeatures) {	
			for (IConstraint constraint : feature.getStructure().getRelevantConstraints()) {
				Node node = constraint.getNode();
				if (node instanceof Equals) {
					Node[] children = node.getChildren();
					Node leftChild = children[0];
					Node rightChild = children[1];
					if (leftChild instanceof Literal && ((Literal) leftChild).var.equals(feature.getName())) {
						IConstraint	rightConstraint = FMFactoryManager.getFactory().createConstraint(fm, rightChild);
						rightConstraint.setContainedFeatures();
						if (!rightConstraint.hasHiddenFeatures()) {
							list.add(feature);
							break;
						}
					}
					if (rightChild instanceof Literal &&  ((Literal) rightChild).var.equals(feature.getName())) {
						IConstraint  leftConstraint = FMFactoryManager.getFactory().createConstraint(fm, leftChild);
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
		for (IFeature feature: hiddenFeatures) {
			if (canceled()) {
				return;
			}
			setSubTask(CALCULATE_INDETRMINATE_HIDDEN_FEATURES_FOR + feature.getName());
			if (!list.contains(feature)) {
				Collection<IFeature> set = featureDependencies.getImpliedFeatures(feature);
				boolean noHidden = false;
				for (IFeature f : set) {
					if (!f.getStructure().isHidden() && !f.getStructure().hasHiddenParent() || list.contains(f)) {
						if (featureDependencies.isAlways(f, feature)) {
							noHidden = true; 
							break;
						}
					}
				}	

				if (!noHidden) {
					changedAttributes.put(feature, FeatureStatus.INDETERMINATE_HIDDEN);					
					feature.getProperty().setFeatureStatus(FeatureStatus.INDETERMINATE_HIDDEN, false);
				}
				
				worked(1);
			}
		}
	}
	
	/**
	 * Gets all hidden features their children
	 * @return
	 */
	public Collection<IFeature> getHiddenFeatures() {
		Collection<IFeature> hiddenFeatures = new LinkedList<IFeature>();
		for (IFeature f : fm.getFeatures()) {
			if (f.getStructure().isHidden() || f.getStructure().hasHiddenParent()) {
				hiddenFeatures.add(f);
			}
		}
		return hiddenFeatures;
	}

	private void getFalseOptionalFeature(Map<Object, Object> oldAttributes,
			Map<Object, Object> changedAttributes) {
		chachedFalseOptionalFeatures.clear();
		for (IFeature f : getFalseOptionalFeatures()) {
			changedAttributes.put(f,FeatureStatus.FALSE_OPTIONAL);
			f.getProperty().setFeatureStatus(FeatureStatus.FALSE_OPTIONAL, false);
			chachedFalseOptionalFeatures.add(f);
		}
	}

	public List<IFeature> getFalseOptionalFeatures() {
		return getFalseOptionalFeatures(fm.getFeatures());
	}
	
	public List<IFeature> getFalseOptionalFeatures(Iterable<IFeature> fmFalseOptionals) {
		final List<IFeature> falseOptionalFeatures = new ArrayList<>();

		final SatSolver solver = new SatSolver(AdvancedNodeCreator.createCNF(fm), 1000);
		for (IFeature feature : fmFalseOptionals) {
			final IFeatureStructure structure = feature.getStructure();
			final IFeature parent = FeatureUtils.getParent(feature);
			if (!structure.isMandatory() && parent != null && solver.isImplied(
					new Literal(parent.getName(), false),
					new Literal(feature.getName()))) {
				falseOptionalFeatures.add(feature);
			}
		}
		return falseOptionalFeatures;
	}

	public int countConcreteFeatures() {
		int number = 0;
		for (IFeature feature : fm.getFeatures())
			if (feature.getStructure().isConcrete())
				number++;
		return number;
	}

	public int countHiddenFeatures() {
		int number = 0;
		for (IFeature feature : fm.getFeatures()) {
			final IFeatureStructure structure = feature.getStructure();
			if (structure.isHidden() || structure.hasHiddenParent()) {
				number++;
			}
		}
		return number;
	}

	public int countTerminalFeatures() {
		int number = 0;
		for (IFeature feature : fm.getFeatures())
			if (!feature.getStructure().hasChildren())
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

	public List<IFeature> getCachedDeadFeatures() {
		return Collections.unmodifiableList(cachedDeadFeatures);
	}

	public List<IFeature> getCachedCoreFeatures() {
		return Collections.unmodifiableList(cachedCoreFeatures);
	}

	public boolean getAttributeFlag(Attribute attribute) {
		return attributeFlags[attribute.ordinal()];
	}
	
	public void setAttributeFlag(Attribute attribute, boolean flag) {
		attributeFlags[attribute.ordinal()] = flag;
	}
	
	public void resetAttributeFlags() {
		Arrays.fill(attributeFlags, false);
	}

}
