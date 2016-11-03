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
package org.prop4j.analyses;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Equals;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.ModifiableSolver;
import org.prop4j.solver.SatInstance;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.explanations.DeadFeature;
import de.ovgu.featureide.fm.core.explanations.FalseOptionalFeature;
import de.ovgu.featureide.fm.core.explanations.RedundantConstraint;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * A collection of methods for working with {@link IFeatureModel} will replace
 * the corresponding methods in {@link IFeatureModel}
 * 
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelAnalysis implements LongRunningMethod<HashMap<Object, Object>> {

	/**
	 * Used for tool tip: remember explanation for redundant constraint.
	 * Key = constraintIndex, Value = explanation
	 */
	public HashMap<Integer, List<String>> redundantConstrExpl = new HashMap<>();

	/**
	 * Used for tool tip: remember explanation for redundant constraint.
	 * Key = constraintIndex, Value = explanation
	 */
	public HashMap<IFeature, List<String>> deadFeatureExpl = new HashMap<>();

	/**
	 * Used for tool tip: remember explanation for redundant constraint.
	 * Key = constraintIndex, Value = explanation
	 */
	public HashMap<IFeature, List<String>> falseOptFeatureExpl = new HashMap<>();

	/**
	 * Defines whether constraints should be included into calculations.
	 */
	public boolean calculateConstraints = true;

	/**
	 * Defines whether features should be included into calculations.
	 * If features are not analyzed, then constraints a also NOT analyzed.
	 */
	public boolean calculateFeatures = true;

	/**
	 * Defines whether redundant constraints should be calculated.
	 */
	public boolean calculateRedundantConstraints = true;

	public boolean calculateFOConstraints = true;

	public boolean calculateDeadConstraints = true;

	/**
	 * Defines whether constraints that are tautologies should be calculated.
	 */
	public boolean calculateTautologyConstraints = true;

	public boolean calculateExplanations = true;

	private final HashMap<Object, Object> changedAttributes = new HashMap<>();

	private boolean valid;
	private final List<IFeature> coreFeatures;
	private final List<IFeature> deadFeatures;
	private final List<IFeature> falseOptionalFeatures;

	private final IFeatureModel fm;
	private final IFeatureModelFactory factory;
	private final AdvancedNodeCreator nodeCreator;

	private IMonitor monitor = new NullMonitor();

	public FeatureModelAnalysis(IFeatureModel fm) {
		this.fm = fm;
		this.factory = FMFactoryManager.getFactory(fm);

		deadFeatures = new ArrayList<>();
		coreFeatures = new ArrayList<>();
		falseOptionalFeatures = new ArrayList<>();

		nodeCreator = new AdvancedNodeCreator(fm);
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		nodeCreator.setUseOldNames(false);
	}

	public boolean isCalculateConstraints() {
		return calculateConstraints;
	}

	public boolean isCalculateFeatures() {
		return calculateFeatures;
	}

	public boolean isCalculateRedundantConstraints() {
		return calculateRedundantConstraints;
	}

	public boolean isCalculateTautologyConstraints() {
		return calculateTautologyConstraints;
	}

	public boolean isValid() {
		return valid;
	}

	public List<IFeature> getCoreFeatures() {
		return coreFeatures;
	}

	public List<IFeature> getDeadFeatures() {
		return deadFeatures;
	}

	public List<IFeature> getFalseOptionalFeatures() {
		return falseOptionalFeatures;
	}

	public void setCalculateConstraints(boolean calculateConstraints) {
		this.calculateConstraints = calculateConstraints;
	}

	public void setCalculateFeatures(boolean calculateFeatures) {
		this.calculateFeatures = calculateFeatures;
	}

	public void setCalculateRedundantConstraints(boolean calculateRedundantConstraints) {
		this.calculateRedundantConstraints = calculateRedundantConstraints;
	}

	public void setCalculateTautologyConstraints(boolean calculateTautologyConstraints) {
		this.calculateTautologyConstraints = calculateTautologyConstraints;
	}

	public void setCalculateFOConstraints(boolean calculateFOConstraints) {
		this.calculateFOConstraints = calculateFOConstraints;
	}

	public void setCalculateDeadConstraints(boolean calculateDeadConstraints) {
		this.calculateDeadConstraints = calculateDeadConstraints;
	}

	public void setCalculateExplanations(boolean calculateExplanations) {
		this.calculateExplanations = calculateExplanations;
	}

	/**
	 * @return Hashmap: key entry is Feature/Constraint, value usually
	 *         indicating the kind of attribute (non-Javadoc)
	 */
	@Override
	public HashMap<Object, Object> execute(IMonitor monitor) throws Exception {
		this.monitor = monitor;
		int work = 0;
		if (calculateFeatures) {
			work += 5;
			if (calculateConstraints) {
				work += 2;
			}
		}
		monitor.setRemainingWork(work);

		changedAttributes.clear();

		deadFeatures.clear();
		coreFeatures.clear();
		falseOptionalFeatures.clear();

		// put root always in so it will be refreshed (void/non-void)
		changedAttributes.put(fm.getStructure().getRoot().getFeature(), FeatureStatus.NORMAL);

		valid = true;

		if (calculateFeatures) {
			monitor.checkCancel();
			updateFeatures();

			if (calculateConstraints) {
				monitor.checkCancel();
				updateConstraints();
			}
		}

		return changedAttributes;
	}

	public void updateFeatures() {
		final Iterable<IFeature> features = fm.getFeatures();
		for (IFeature feature : features) {
			feature.getProperty().setFeatureStatus(FeatureStatus.NORMAL, false);
			FeatureUtils.setRelevantConstraints(feature);
		}
		monitor.step();

		nodeCreator.setModelType(ModelType.All);
		final SatInstance si = new SatInstance(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));

		checkValidity(si);
		monitor.step();

		if (valid) {
			checkFeatureFalseOptional(features, si);
			monitor.step();

			checkFeatureDead(si);
			monitor.step();

			checkFeatureHidden(features);
			monitor.step();
		}
	}

	public void updateConstraints() {
		final List<IConstraint> constraints = fm.getConstraints();
		for (IConstraint constraint : constraints) {
			constraint.setConstraintAttribute(ConstraintAttribute.NORMAL, false);
			constraint.setContainedFeatures();
			constraint.setFalseOptionalFeatures(Collections.<IFeature> emptyList());
			constraint.setDeadFeatures(Collections.<IFeature> emptyList());
		}

		if (!calculateFeatures) {
			checkValidity(new SatInstance(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm)));
		}

		try {
			if (valid) {
				checkConstraintRedundant(constraints);
				monitor.step();
				checkConstraintDeadAndFalseOptional(constraints);
				monitor.step();
			} else {
				checkConstraintUnsatisfiable(constraints);
				monitor.step();
				monitor.step();
			}
		} catch (ContradictionException e) {
			Logger.logError(e);
		}
	}

	private boolean checkConstraintContradiction(Node constraintNode) {
		return LongRunningWrapper.runMethod(new ValidAnalysis(new SatInstance(constraintNode))) == null;
	}

	private void checkConstraintDeadAndFalseOptional(final List<IConstraint> constraints) throws ContradictionException {
		if (!calculateFOConstraints && !calculateDeadConstraints) {
			return;
		}
		nodeCreator.setModelType(ModelType.OnlyStructure);
		final SatInstance si = new SatInstance(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		final BasicSolver modSat = new BasicSolver(si);

		final List<IFeature> deadList = new LinkedList<>(deadFeatures);
		final List<IFeature> foList = new LinkedList<>(falseOptionalFeatures);
		monitor.checkCancel();

		for (IConstraint constraint : constraints) {
			modSat.addClauses(makeRegular(constraint.getNode()));

			if (constraint.getConstraintAttribute() == ConstraintAttribute.NORMAL) {
				if (calculateDeadConstraints) {
					final List<IFeature> newDeadFeature = checkFeatureDead2(modSat, deadList);
					if (!newDeadFeature.isEmpty()) {
						constraint.setDeadFeatures(newDeadFeature);
						deadList.removeAll(newDeadFeature);
						setConstraintAttribute(constraint, ConstraintAttribute.DEAD);
					}
				}

				if (calculateFOConstraints) {
					final List<IFeature> newFOFeature = checkFeatureFalseOptional2(modSat, foList);
					if (!newFOFeature.isEmpty()) {
						constraint.setFalseOptionalFeatures(newFOFeature);
						foList.removeAll(newFOFeature);
						if (constraint.getConstraintAttribute() == ConstraintAttribute.NORMAL) {
							setConstraintAttribute(constraint, ConstraintAttribute.FALSE_OPTIONAL);
						}
					}
				}
			}
			monitor.checkCancel();
		}
	}

	/**
	 * Detects redundancy of a constraint by checking if the model without the new (possibly redundant) constraint
	 * implies the model with the new constraint and the other way round. If this is the case, both models are
	 * equivalent and the constraint is redundant.
	 * If a redundant constraint has been detected, it is explained.
	 * 
	 * @param constraint The constraint to check whether it is redundant
	 */
	private void checkConstraintRedundant(final List<IConstraint> constraints) throws ContradictionException {
		if (calculateRedundantConstraints) {
			final IFeatureModel clone = fm.clone();
			nodeCreator.setModelType(ModelType.OnlyStructure);
			final SatInstance si = new SatInstance(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
			final ModifiableSolver redundantSat = new ModifiableSolver(si);

			final List<List<IConstr>> constraintMarkers = new ArrayList<>();
			final List<Node> cnfNodes = new ArrayList<>();
			for (IConstraint constraint : constraints) {
				Node cnf = makeRegular(constraint.getNode());
				cnfNodes.add(cnf);

				constraintMarkers.add(redundantSat.addClauses(cnf));
			}
			monitor.checkCancel();

			int i = -1;
			for (IConstraint constraint : constraints) {
				i++;
				if (calculateRedundantConstraints) {
					boolean redundant = true;
					boolean removedAtLeastOne = false;
					for (IConstr cm : constraintMarkers.get(i)) {
						if (cm != null) {
							removedAtLeastOne = true;
							redundantSat.removeConstraint(cm);
						}
					}
					if (removedAtLeastOne) {
						final Node constraintNode = cnfNodes.get(i);

						final Node[] clauses = constraintNode.getChildren();
						for (int j = 0; j < clauses.length; j++) {
							if (!redundantSat.isImplied(clauses[j].getChildren())) {
								redundant = false;
								redundantSat.addClauses(constraintNode);
								break;
							}
						}
					}

					if (redundant) {
						clone.removeConstraint(constraint);
						if (checkConstraintTautology(constraint.getNode())) {
							setConstraintAttribute(constraint, ConstraintAttribute.TAUTOLOGY);
						} else {
							setConstraintAttribute(constraint, ConstraintAttribute.REDUNDANT);

							if (calculateExplanations) {
								RedundantConstraint redundancy = new RedundantConstraint();
								List<String> expl = redundancy.explain(clone, constraint); //store explanation for redundant constraint
								redundantConstrExpl.put(FeatureUtils.getConstraintIndex(fm, constraint), expl);
							}
						}
					}
				}
				monitor.checkCancel();
			}
		} else if (calculateTautologyConstraints) {
			for (IConstraint constraint : constraints) {
				if (checkConstraintTautology(constraint.getNode())) {
					setConstraintAttribute(constraint, ConstraintAttribute.TAUTOLOGY);
				}
				monitor.checkCancel();
			}
		}
	}

	private boolean checkConstraintTautology(Node constraintNode) {
		return checkConstraintContradiction(makeRegular(new Not(constraintNode)));
	}

	private void checkConstraintUnsatisfiable(final List<IConstraint> constraints) throws ContradictionException {
		nodeCreator.setModelType(ModelType.OnlyStructure);
		final SatInstance si = new SatInstance(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		final ModifiableSolver unsat = new ModifiableSolver(si);
		monitor.checkCancel();

		for (IConstraint constraint : constraints) {
			Node cnf = makeRegular(constraint.getNode());

			List<IConstr> constraintMarkers = null;
			boolean satisfiable;
			try {
				constraintMarkers = unsat.addClauses(cnf);
				satisfiable = unsat.isSatisfiable() == SatResult.TRUE;
			} catch (ContradictionException e) {
				satisfiable = false;
			}

			if (!satisfiable) {
				if (constraintMarkers != null) {
					for (IConstr constr : constraintMarkers) {
						if (constr != null) {
							unsat.removeConstraint(constr);
						}
					}

					if (checkConstraintContradiction(cnf)) {
						setConstraintAttribute(constraint, ConstraintAttribute.UNSATISFIABLE);
						if (calculateExplanations) {
							explainVoidFM();
						}
					} else {
						setConstraintAttribute(constraint, ConstraintAttribute.VOID_MODEL);
						if (calculateExplanations) {
							explainVoidFM();
						}
					}
				} else {
					setConstraintAttribute(constraint, ConstraintAttribute.UNSATISFIABLE);
					if (calculateExplanations) {
						explainVoidFM();
					}
				}
			}
			monitor.checkCancel();
		}
	}

	// explain void feature model, treat root as dead feature
	private void explainVoidFM() {
		DeadFeature deadF = new DeadFeature();
		List<String> expl = deadF.explain(fm, FeatureUtils.getRoot(fm), true);
		deadFeatureExpl.put(FeatureUtils.getRoot(fm), expl);
	}

	private void checkFeatureDead(final SatInstance si) {
		deadFeatures.clear();
		coreFeatures.clear();
		final int[] solution2 = LongRunningWrapper.runMethod(new CoreDeadAnalysis(si), monitor.subTask(0));
		monitor.checkCancel();
		for (int i = 0; i < solution2.length; i++) {
			monitor.checkCancel();
			final int var = solution2[i];
			final IFeature feature = fm.getFeature((String) si.getVariableObject(var));
			if (var < 0) {
				setFeatureAttribute(feature, FeatureStatus.DEAD);
				deadFeatures.add(feature);

				if (calculateExplanations) {
					// explain dead features and remember explanation in map
					DeadFeature deadF = new DeadFeature();
					List<String> expl = deadF.explain(fm, feature, false);
					deadFeatureExpl.put(feature, expl);

				} else {
					coreFeatures.add(feature);
				}
			}
		}
	}

	private List<IFeature> checkFeatureDead2(final BasicSolver solver, List<IFeature> deadList) {
		if (deadList.size() == 0) {
			return Collections.emptyList();
		}
		final List<IFeature> result = new ArrayList<>();
		int[] deadVar = new int[deadList.size()];
		int j = 0;
		for (IFeature deadFeature : deadList) {
			deadVar[j++] = solver.getSatInstance().getVariable(deadFeature.getName());
		}
		final int[] solution2 = LongRunningWrapper.runMethod(new CoreDeadAnalysis(solver, deadVar));
		for (int i = 0; i < solution2.length; i++) {
			final int var = solution2[i];
			if (var < 0) {
				result.add(fm.getFeature((String) solver.getSatInstance().getVariableObject(var)));
			}
		}
		return result;
	}

	private void checkFeatureFalseOptional(final Iterable<IFeature> features, final SatInstance si) {
		final List<int[]> possibleFOFeatures = new ArrayList<>();
		for (IFeature feature : features) {
			final IFeature parent = FeatureUtils.getParent(feature);
			if (parent != null && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
				possibleFOFeatures.add(new int[] { -si.getVariable(parent.getName()), si.getVariable(feature.getName()) });
			}
		}
		final List<int[]> solution3 = LongRunningWrapper.runMethod(new ImplicationAnalysis(si, possibleFOFeatures), monitor.subTask(0));
		monitor.checkCancel();
		falseOptionalFeatures.clear();
		for (int[] pair : solution3) {
			monitor.checkCancel();
			final IFeature feature = fm.getFeature((CharSequence) si.getVariableObject(pair[1]));
			setFeatureAttribute(feature, FeatureStatus.FALSE_OPTIONAL);
			falseOptionalFeatures.add(feature);

			if (calculateExplanations) {
				// explain false optional features and remember explanation in map
				FalseOptionalFeature falseOpts = new FalseOptionalFeature();
				List<String> expl = falseOpts.explain(fm, feature);
				falseOptFeatureExpl.put(feature, expl);
			}
		}
	}

	private List<IFeature> checkFeatureFalseOptional2(final BasicSolver solver, List<IFeature> foList) {
		if (foList.size() == 0) {
			return Collections.emptyList();
		}
		final List<IFeature> result = new ArrayList<>();
		final List<int[]> possibleFOFeatures = new ArrayList<>();
		final SatInstance si = solver.getSatInstance();
		for (IFeature feature : foList) {
			final IFeature parent = FeatureUtils.getParent(feature);
			if (parent != null && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
				possibleFOFeatures.add(new int[] { -si.getVariable(parent.getName()), si.getVariable(feature.getName()) });
			}
		}
		final List<int[]> solution3 = LongRunningWrapper.runMethod(new ImplicationAnalysis(solver, possibleFOFeatures));
		for (int[] pair : solution3) {
			result.add(fm.getFeature((CharSequence) si.getVariableObject(pair[1])));
		}
		return result;
	}

	/**
	 * Calculations for indeterminate hidden features
	 * 
	 * @param changedAttributes
	 */
	private void checkFeatureHidden(final Iterable<IFeature> features) {
		if (!fm.getStructure().hasHidden()) {
			return;
		}
		/**
		 * First every relevant constraint of every hidden feature is checked if its form equals
		 * HIDDEN_FEATURE <=> A
		 * where A is an expression containing only non hidden features
		 * If there is a constraint of that kind for a hidden feature it is added to a list.
		 */
		Collection<IFeature> list = new LinkedList<>();
		Collection<IFeature> hiddenFeatures = Functional.toList(Functional.filter(features, new HiddenFeatureFilter()));
		for (IFeature feature : hiddenFeatures) {
			monitor.checkCancel();
			for (IConstraint constraint : feature.getStructure().getRelevantConstraints()) {
				Node node = constraint.getNode();
				if (node instanceof Equals) {
					Node[] children = node.getChildren();
					Node leftChild = children[0];
					Node rightChild = children[1];
					if (leftChild instanceof Literal && ((Literal) leftChild).var.equals(feature.getName())) {
						IConstraint rightConstraint = factory.createConstraint(fm, rightChild);
						rightConstraint.setContainedFeatures();
						if (!rightConstraint.hasHiddenFeatures()) {
							list.add(feature);
							break;
						}
					}
					if (rightChild instanceof Literal && ((Literal) rightChild).var.equals(feature.getName())) {
						IConstraint leftConstraint = factory.createConstraint(fm, leftChild);
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
		 * - has a non-hidden Node in its atomic set defining its state or
		 * - if a Node of its atomic set is determined by a constraint of the above form.
		 */
		FeatureDependencies featureDependencies = new FeatureDependencies(fm, false);
		for (IFeature feature : hiddenFeatures) {
			monitor.checkCancel();
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
					setFeatureAttribute(feature, FeatureStatus.INDETERMINATE_HIDDEN);
				}
			}
		}
	}

	private void checkValidity(final SatInstance si) {
		valid = LongRunningWrapper.runMethod(new ValidAnalysis(si)) != null;
	}

	private Node makeRegular(Node node) {
		Node regularCNFNode = node.toCNF();
		if (regularCNFNode instanceof And) {
			final Node[] children = regularCNFNode.getChildren();
			for (int i = 0; i < children.length; i++) {
				final Node child = children[i];
				if (child instanceof Literal) {
					children[i] = new Or(child);
				}
			}
		} else if (regularCNFNode instanceof Or) {
			regularCNFNode = new And(regularCNFNode);
		} else if (regularCNFNode instanceof Literal) {
			regularCNFNode = new And(new Or(regularCNFNode));
		}
		return regularCNFNode;
	}

	private void setFeatureAttribute(IFeature feature, FeatureStatus featureAttribute) {
		changedAttributes.put(feature, featureAttribute);
		feature.getProperty().setFeatureStatus(featureAttribute, false);
	}

	private void setConstraintAttribute(IConstraint constraint, ConstraintAttribute constraintAttribute) {
		changedAttributes.put(constraint, constraintAttribute);
		constraint.setConstraintAttribute(constraintAttribute, false);
	}

}
