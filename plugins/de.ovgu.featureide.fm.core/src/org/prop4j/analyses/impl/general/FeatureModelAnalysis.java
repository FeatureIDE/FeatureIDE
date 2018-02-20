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
package org.prop4j.analyses.impl.general;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.impl.SatProblem;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * A collection of methods for working with {@link IFeatureModel} will replace the corresponding methods in {@link IFeatureModel}
 *
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelAnalysis implements LongRunningMethod<HashMap<Object, Object>> {

	/**
	 * Defines whether constraints should be included into calculations.
	 */
	public boolean calculateConstraints = true;

	/**
	 * Defines whether features should be included into calculations. If features are not analyzed, then constraints a also NOT analyzed.
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

	private final HashMap<Object, Object> changedAttributes = new HashMap<>();

	private boolean valid;
	private final List<IFeature> coreFeatures;
	private final List<IFeature> deadFeatures;
	private final List<IFeature> falseOptionalFeatures;

	private final IFeatureModel fm;
	private final AdvancedNodeCreator nodeCreator;

	protected SatProblem allModelProblem;
	protected SatProblem structureModelProblem;
	protected SatProblem constraintModelProblem;

	private IMonitor monitor = new NullMonitor();

	AbstractSolverAnalysisFactory factory;

	public FeatureModelAnalysis(IFeatureModel fm) {
		this.fm = fm;

		deadFeatures = new ArrayList<>();
		coreFeatures = new ArrayList<>();
		falseOptionalFeatures = new ArrayList<>();

		nodeCreator = new AdvancedNodeCreator(fm);
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		nodeCreator.setUseOldNames(false);

		// Only create the cnf one time for every mode
		nodeCreator.setModelType(ModelType.All);
		allModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		nodeCreator.setModelType(ModelType.OnlyStructure);
		structureModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		nodeCreator.setModelType(ModelType.OnlyConstraints);
		constraintModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));

		factory = AbstractSolverAnalysisFactory.getJavaSmtSatFactory();
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

	/**
	 * @return Hashmap: key entry is Feature/Constraint, value usually indicating the kind of attribute (non-Javadoc)
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
		if ((fm != null) && (fm.getStructure() != null) && (fm.getStructure().getRoot() != null) && (fm.getStructure().getRoot().getFeature() != null)) {
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
		}
		return changedAttributes;
	}

	public void updateFeatures() {
		final Iterable<IFeature> features = fm.getFeatures();
		for (final IFeature feature : features) {
			feature.getProperty().setFeatureStatus(FeatureStatus.NORMAL, false);
			FeatureUtils.setRelevantConstraints(feature);
		}
		monitor.step();

		checkValidity(allModelProblem);

		monitor.step();

		if (valid) {
			checkFeatureFalseOptional(features);
			monitor.step();

			checkFeatureDead();
			monitor.step();

			checkFeatureHidden(features);
			monitor.step();
		}
	}

	private void checkValidity(final SatProblem modelProblem) {
		final ValidAnalysis validAnalysis = (ValidAnalysis) factory.getAnalysis(ValidAnalysis.class, modelProblem);
		valid = LongRunningWrapper.runMethod(validAnalysis) != null;
		if (!valid) {
			changedAttributes.put(fm.getStructure().getRoot().getFeature(), FeatureStatus.DEAD);
		}
	}

	private void checkFeatureDead() {
		deadFeatures.clear();
		coreFeatures.clear();

		final org.prop4j.analyses.impl.general.CoreDeadAnalysis coreDeadAnalysis =
			(org.prop4j.analyses.impl.general.CoreDeadAnalysis) factory.getAnalysis(org.prop4j.analyses.impl.general.CoreDeadAnalysis.class, allModelProblem);

		final int[] solution2 = LongRunningWrapper.runMethod(coreDeadAnalysis, monitor.subTask(0));

		monitor.checkCancel();
		for (int i = 0; i < solution2.length; i++) {
			monitor.checkCancel();
			final int var = solution2[i];
			final IFeature feature = fm.getFeature((String) allModelProblem.getVariableOfIndex(var));
			if (var < 0) {
				setFeatureAttribute(feature, FeatureStatus.DEAD);
				deadFeatures.add(feature);
			} else {
				coreFeatures.add(feature);
			}
		}
	}

	private void checkFeatureFalseOptional(final Iterable<IFeature> features) {
		final List<int[]> possibleFOFeatures = new ArrayList<>();
		for (final IFeature feature : features) {
			final IFeature parent = FeatureUtils.getParent(feature);
			if ((parent != null) && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
				possibleFOFeatures
						.add(new int[] { -allModelProblem.getIndexOfVariable(parent.getName()), allModelProblem.getIndexOfVariable(feature.getName()) });
			}
		}

		final ImplicationAnalysis implicationAnalysis = (ImplicationAnalysis) factory.getAnalysis(ImplicationAnalysis.class, allModelProblem);
		implicationAnalysis.initParis(possibleFOFeatures);
		final List<int[]> solution3 = LongRunningWrapper.runMethod(implicationAnalysis, monitor.subTask(0));

		monitor.checkCancel();
		falseOptionalFeatures.clear();
		for (final int[] pair : solution3) {
			monitor.checkCancel();
			final IFeature feature = fm.getFeature((CharSequence) allModelProblem.getVariableOfIndex(pair[1]));
			setFeatureAttribute(feature, FeatureStatus.FALSE_OPTIONAL);
			falseOptionalFeatures.add(feature);
		}
	}

	/**
	 * // * Calculations for indeterminate hidden features // * // * @param changedAttributes //
	 */
	private void checkFeatureHidden(final Iterable<IFeature> features) {
		if (!fm.getStructure().hasHidden()) {
			return;
		}

		final Iterable<IFeature> hiddenFeatures = Functional.filter(features, new HiddenFeatureFilter());
		final List<String> hiddenLiterals = Functional.toList(Functional.map(hiddenFeatures, new Functional.IFunction<IFeature, String>() {

			@Override
			public String invoke(IFeature feature) {
				return feature.getName();
			}
		}));
		final org.prop4j.analyses.impl.general.IndeterminedAnalysis indeterminedAnalysis = (org.prop4j.analyses.impl.general.IndeterminedAnalysis) factory
				.getAnalysis(org.prop4j.analyses.impl.general.IndeterminedAnalysis.class, allModelProblem);
		indeterminedAnalysis.init(hiddenLiterals);
		final int[] determinedHidden = LongRunningWrapper.runMethod(indeterminedAnalysis);

		for (final int feature : determinedHidden) {
			setFeatureAttribute(fm.getFeature(allModelProblem.getVariableOfIndex(feature).toString()), FeatureStatus.INDETERMINATE_HIDDEN);
		}
	}

	private void setFeatureAttribute(IFeature feature, FeatureStatus featureAttribute) {
		changedAttributes.put(feature, featureAttribute);
		feature.getProperty().setFeatureStatus(featureAttribute, false);
	}

	private void setConstraintAttribute(IConstraint constraint, ConstraintAttribute constraintAttribute) {
		changedAttributes.put(constraint, constraintAttribute);
		constraint.setConstraintAttribute(constraintAttribute, false);
	}

	public void updateConstraints() {
		final List<IConstraint> constraints = fm.getConstraints();
		for (final IConstraint constraint : constraints) {
			constraint.setConstraintAttribute(ConstraintAttribute.NORMAL, false);
			constraint.setContainedFeatures();
			constraint.setFalseOptionalFeatures(Collections.<IFeature> emptyList());
			constraint.setDeadFeatures(Collections.<IFeature> emptyList());
		}

		if (!calculateFeatures) {
			checkValidity(allModelProblem);
		}

		try {
			if (valid) {
				checkConstraintRedundant(constraints);
				monitor.step();
//				checkConstraintDeadAndFalseOptional(constraints);
				monitor.step();
			} else {
				checkConstraintUnsatisfiable(constraints);
				monitor.step();
				monitor.step();
			}
		} catch (final ContradictionException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private boolean checkConstraintContradiction(Node constraintNode) {
		final ISatProblem problem = new SatProblem(constraintNode);
		final ValidAnalysis validAnalysis = (ValidAnalysis) factory.getAnalysis(ValidAnalysis.class, problem);

		return LongRunningWrapper.runMethod(validAnalysis, new NullMonitor()) == null;
	}

//
//	private void checkConstraintDeadAndFalseOptional(final List<IConstraint> constraints) throws ContradictionException {
//		if (!calculateFOConstraints && !calculateDeadConstraints) {
//			return;
//		}
//		nodeCreator.setModelType(ModelType.OnlyStructure);
//		final SatProblem problem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
//		final Sat4jSatSolver modSat = new Sat4jSatSolver(problem);
//
//		final List<IFeature> deadList = new LinkedList<>(deadFeatures);
//		final List<IFeature> foList = new LinkedList<>(falseOptionalFeatures);
//		monitor.checkCancel();
//
//		for (final IConstraint constraint : constraints) {
//			modSat.push(constraint.getNode().toRegularCNF());
//
//			if (constraint.getConstraintAttribute() == ConstraintAttribute.NORMAL) {
//				if (calculateDeadConstraints) {
//					final List<IFeature> newDeadFeature = checkFeatureDead2(modSat, deadList);
//					if (!newDeadFeature.isEmpty()) {
//						constraint.setDeadFeatures(newDeadFeature);
//						deadList.removeAll(newDeadFeature);
//						setConstraintAttribute(constraint, ConstraintAttribute.DEAD);
//					}
//				}
//
//				if (calculateFOConstraints) {
//					final List<IFeature> newFOFeature = checkFeatureFalseOptional2(modSat, foList);
//					if (!newFOFeature.isEmpty()) {
//						constraint.setFalseOptionalFeatures(newFOFeature);
//						foList.removeAll(newFOFeature);
//						if (constraint.getConstraintAttribute() == ConstraintAttribute.NORMAL) {
//							setConstraintAttribute(constraint, ConstraintAttribute.FALSE_OPTIONAL);
//						}
//					}
//				}
//			}
//			monitor.checkCancel();
//		}
//	}
//
//	private List<IFeature> checkFeatureDead2(final ISolverProblem problem, List<IFeature> deadList) {
//		if (deadList.size() == 0) {
//			return Collections.emptyList();
//		}
//		final List<IFeature> result = new ArrayList<>();
//		final int[] deadVar = new int[deadList.size()];
//		int j = 0;
//		for (final IFeature deadFeature : deadList) {
//			deadVar[j++] = problem.getIndexOfVariable(deadFeature.getName());
//		}
//
//		final org.prop4j.analyses.impl.general.CoreDeadAnalysis coreDeadAnalysis =
//			(org.prop4j.analyses.impl.general.CoreDeadAnalysis) factory.getAnalysis(org.prop4j.analyses.impl.general.CoreDeadAnalysis.class, problem);
//		coreDeadAnalysis.setFeatures(deadVar);
//
//		final int[] solution2 = LongRunningWrapper.runMethod(coreDeadAnalysis);
//
//		for (int i = 0; i < solution2.length; i++) {
//			final int var = solution2[i];
//			if (var < 0) {
//				result.add(fm.getFeature((String) problem.getVariableOfIndex(var)));
//			}
//		}
//		return result;
//	}
//
//	private List<IFeature> checkFeatureFalseOptional2(final BasicSolver solver, List<IFeature> foList) {
//		if (foList.size() == 0) {
//			return Collections.emptyList();
//		}
//		final List<IFeature> result = new ArrayList<>();
//		final List<int[]> possibleFOFeatures = new ArrayList<>();
//		final SatInstance si = solver.getSatInstance();
//		for (final IFeature feature : foList) {
//			final IFeature parent = FeatureUtils.getParent(feature);
//			if ((parent != null) && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
//				possibleFOFeatures.add(new int[] { -si.getVariable(parent.getName()), si.getVariable(feature.getName()) });
//			}
//		}
//		final List<int[]> solution3 = LongRunningWrapper.runMethod(new ImplicationAnalysis(solver, possibleFOFeatures));
//
//		for (final int[] pair : solution3) {
//			result.add(fm.getFeature((CharSequence) si.getVariableObject(pair[1])));
//		}
//
//		if (evaluate) {
//			final ISolverProblem problem = new SatProblem(si.getCnf(), FeatureUtils.getFeatureNamesPreorder(fm));
//			final org.prop4j.analyses.impl.general.ImplicationAnalysis implicationAnalysis =
//				(org.prop4j.analyses.impl.general.ImplicationAnalysis) factory.getAnalysis(org.prop4j.analyses.impl.general.ImplicationAnalysis.class, problem);
//			implicationAnalysis.initParis(possibleFOFeatures);
//			final List<int[]> solution4 = LongRunningWrapper.runMethod(implicationAnalysis);
//
//			final ArrayList<IFeature> result2 = new ArrayList<>();
//			for (final int[] pair : solution4) {
//				result2.add(fm.getFeature((CharSequence) si.getVariableObject(pair[1])));
//			}
//			analysisComparison += "checkFeatureFalseOptional2:\nO: " + result.toString() + "\nN: " + result2.toString() + "\n\n";
//		}
//
//		return result;
//	}
//
	/**
	 * Detects redundancy of a constraint by checking if the model without the new (possibly redundant) constraint implies the model with the new constraint and
	 * the other way round. If this is the case, both models are equivalent and the constraint is redundant. If a redundant constraint has been detected, it is
	 * explained.
	 *
	 * @param constraint The constraint to check whether it is redundant
	 */
	private void checkConstraintRedundant(final List<IConstraint> constraints) throws ContradictionException {
		if (calculateRedundantConstraints) {
			final RedundantConstraintAnalysis redundantAnalysis =
				(RedundantConstraintAnalysis) factory.getAnalysis(RedundantConstraintAnalysis.class, structureModelProblem);
			redundantAnalysis.setConstraints(constraints);

			final Map<IConstraint, ConstraintAttribute> map = LongRunningWrapper.runMethod(redundantAnalysis, monitor.subTask(0));
			for (final IConstraint iConstraint : map.keySet()) {
				setConstraintAttribute(iConstraint, map.get(iConstraint));
			}
		} else if (calculateTautologyConstraints) {
			for (final IConstraint constraint : constraints) {
				if (checkConstraintTautology(constraint.getNode())) {
					setConstraintAttribute(constraint, ConstraintAttribute.TAUTOLOGY);
				}
				monitor.checkCancel();
			}
		}
	}

	private boolean checkConstraintTautology(Node constraintNode) {
		return checkConstraintContradiction(new Not(constraintNode).toRegularCNF());
	}

	private void checkConstraintUnsatisfiable(final List<IConstraint> constraints) throws ContradictionException {
		// Only structure problem needed
		final ConstraintsUnsatisfiableAnaylsis constraintsUnsatisfiableAnaylsis =
			(ConstraintsUnsatisfiableAnaylsis) factory.getAnalysis(ConstraintsUnsatisfiableAnaylsis.class, structureModelProblem);
		constraintsUnsatisfiableAnaylsis.setConstraints(constraints);
		final Map<IConstraint, ConstraintAttribute> map = LongRunningWrapper.runMethod(constraintsUnsatisfiableAnaylsis, monitor.subTask(0));
		for (final IConstraint iConstraint : map.keySet()) {
			setConstraintAttribute(iConstraint, map.get(iConstraint));
		}
	}
}
