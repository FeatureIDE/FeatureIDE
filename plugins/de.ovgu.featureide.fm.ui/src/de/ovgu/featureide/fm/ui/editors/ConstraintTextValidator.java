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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.List;

import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.analyses.ConditionallyCoreDeadAnalysis;
import org.prop4j.analyses.CoreDeadAnalysis;
import org.prop4j.analyses.ImplicationAnalysis;
import org.prop4j.analyses.ValidAnalysis;
import org.prop4j.solver.BasicSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.SatInstance;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IJob.JobStatus;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
import de.ovgu.featureide.fm.core.job.JobToken;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog.DialogState;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog.ValidationMessage;

/**
 * Class which contains several tests for {@link ConstraintDialog} text field, which contains user written constraints.
 *
 * @author Marcus Pinnecke
 */
public final class ConstraintTextValidator {

	private InitialAnalysis.InitialResult initialResult;
	private JobToken initToken;
	private JobToken token;

	public void init(IFeatureModel featureModel, IConstraint constraint, final IConsumer<ValidationMessage> onUpdate) {
		initToken = LongRunningWrapper.createToken(JobStartingStrategy.RETURN);
		token = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);
		final IRunner<InitialAnalysis.InitialResult> runner = LongRunningWrapper.getRunner(new InitialAnalysis(featureModel, constraint));
		runner.addJobFinishedListener(new JobFinishListener<InitialAnalysis.InitialResult>() {
			@Override
			public void jobFinished(IJob<InitialAnalysis.InitialResult> finishedJob) {
				final ValidationMessage m = new ValidationMessage("");
				if (finishedJob.getStatus() == JobStatus.OK) {
					initialResult = finishedJob.getResults();
					m.setInitialAnalysisSuccess(true);
				} else {
					m.setInitialAnalysisSuccess(false);
				}
				onUpdate.invoke(m);
			}
		});
		onUpdate.invoke(new ValidationMessage(
				"Executing initial analysis...\nThis may take a while. Although it is not recommended, you can save the unchecked constraint."));
		LongRunningWrapper.startJob(initToken, runner);
	}

	public void cancelValidation() {
		LongRunningWrapper.cancelAllJobs(token);
		LongRunningWrapper.cancelAllJobs(initToken);
	}

	/**
	 * Runs tests not blocking the current GUI thread. The result will be returned each test's result and a separate notification before the first tests starts
	 * and (in case of all test has passed) when the entire series has ended.
	 *
	 * @param constraintText Test to text
	 * @param onUpdate Update mechanism
	 */
	public boolean validateAsync(final Node constraintNode, final IConsumer<ValidationMessage> onUpdate) {
		if (initialResult != null) {
			LongRunningWrapper.startJob(token, LongRunningWrapper.getRunner(new Analysis(initialResult, constraintNode, onUpdate)));
			return true;
		} else {
			return false;
		}
	}

	private static class InitialAnalysis implements LongRunningMethod<InitialAnalysis.InitialResult> {

		private static class InitialResult {
			SatInstance satInstance;
			BasicSolver solver;

			boolean valid;
			int[] deadCore;
			List<int[]> possibleFOFeatures;
		}

		private final IFeatureModel featureModel;
		private final IConstraint constraint;

		public InitialAnalysis(IFeatureModel featureModel, IConstraint constraint) {
			this.featureModel = featureModel;
			this.constraint = constraint;
		}

		@Override
		public InitialResult execute(IMonitor monitor) throws Exception {
			final InitialResult initialResult = new InitialResult();
			final IFeatureModel clone = featureModel.clone();
			if (constraint != null) {
				clone.removeConstraint(constraint);
			}
			final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(clone);
			nodeCreator.setCnfType(CNFType.Regular);
			nodeCreator.setIncludeBooleanValues(false);
			initialResult.satInstance = new SatInstance(nodeCreator.createNodes(), Functional.toList(FeatureUtils.getFeatureNamesList(clone)));
			initialResult.solver = new BasicSolver(initialResult.satInstance);

			monitor.checkCancel();
			initialResult.valid = null != LongRunningWrapper.runMethod(new ValidAnalysis(initialResult.solver), monitor);

			if (initialResult.valid) {

				monitor.checkCancel();
				final int[] deadCoreResult = LongRunningWrapper.runMethod(new CoreDeadAnalysis(initialResult.solver), monitor);
				initialResult.deadCore = deadCoreResult == null ? new int[0] : deadCoreResult;

				monitor.checkCancel();
				initialResult.possibleFOFeatures = new ArrayList<>();
				for (final IFeature feature : clone.getFeatures()) {
					final IFeature parent = FeatureUtils.getParent(feature);
					if ((parent != null) && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
						initialResult.possibleFOFeatures.add(new int[] { -initialResult.satInstance.getVariable(parent.getName()),
							initialResult.satInstance.getVariable(feature.getName()) });
					}
				}

				monitor.checkCancel();
				final List<int[]> foResult =
					LongRunningWrapper.runMethod(new ImplicationAnalysis(initialResult.solver, initialResult.possibleFOFeatures), monitor.subTask(0));
				if (foResult != null) {
					initialResult.possibleFOFeatures.removeAll(foResult);
				}
			}

			return initialResult;
		}

	}

	private static class Analysis implements LongRunningMethod<Void> {

		private final InitialAnalysis.InitialResult initialResult;
		private Node constraintNode;
		private final IConsumer<ValidationMessage> onUpdate;

		public Analysis(InitialAnalysis.InitialResult initialResult, Node constraintNode, IConsumer<ValidationMessage> onUpdate) {
			this.initialResult = initialResult;
			this.constraintNode = constraintNode;
			this.onUpdate = onUpdate;
		}

		@Override
		public Void execute(IMonitor monitor) throws Exception {
			onUpdate.invoke(new ValidationMessage(
					"Checking constraint...\nThis may take a while. Although it is not recommended, you can save the unchecked constraint.",
					DialogState.SAVE_CHANGES_DONT_MIND));

			monitor.checkCancel();
			constraintNode = constraintNode.toRegularCNF();

			monitor.checkCancel();
			BasicSolver solver;
			try {
				solver = new BasicSolver(new SatInstance(constraintNode));
			} catch (final ContradictionException e) {
				onUpdate.invoke(new ValidationMessage("Constraint is a contradiction\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}
			SatResult satResult = solver.isSatisfiable();
			switch (satResult) {
			case FALSE:
				onUpdate.invoke(new ValidationMessage("Constraint is a contradiction\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			case TIMEOUT:
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			case TRUE:
				break;
			default:
				break;
			}

			monitor.checkCancel();
			final Node inverseNode = new Not(constraintNode.clone()).toRegularCNF();
			try {
				solver = new BasicSolver(new SatInstance(inverseNode));
			} catch (final ContradictionException e) {
				onUpdate.invoke(new ValidationMessage("Constraint is a tautology\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}
			satResult = solver.isSatisfiable();
			switch (satResult) {
			case FALSE:
				onUpdate.invoke(new ValidationMessage("Constraint is a tautology\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			case TIMEOUT:
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			case TRUE:
				break;
			default:
				break;
			}

			if (!initialResult.valid) {
				onUpdate.invoke(new ValidationMessage("Constraint successfully checked.\n(Feature model is already void)", DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}

			monitor.checkCancel();
			solver = new BasicSolver(initialResult.satInstance);
			try {
				solver.addClauses(constraintNode);
			} catch (final ContradictionException e) {
				onUpdate.invoke(
						new ValidationMessage("Constraint causes the feature model to be void\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}
			satResult = solver.isSatisfiable();
			switch (satResult) {
			case FALSE:
				onUpdate.invoke(
						new ValidationMessage("Constraint causes the feature model to be void\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			case TIMEOUT:
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			case TRUE:
				break;
			default:
				break;
			}

			monitor.checkCancel();
			final BasicSolver inverseSolver = new BasicSolver(initialResult.satInstance);
			try {
				inverseSolver.addClauses(inverseNode);
			} catch (final ContradictionException e) {
				onUpdate.invoke(new ValidationMessage("Constraint is redundant\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}
			satResult = inverseSolver.isSatisfiable();
			switch (satResult) {
			case FALSE:
				onUpdate.invoke(new ValidationMessage("Constraint is redundant\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			case TIMEOUT:
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			case TRUE:
				break;
			default:
				break;
			}

			monitor.checkCancel();
			final ConditionallyCoreDeadAnalysis method = new ConditionallyCoreDeadAnalysis(solver);
			method.setAssumptions(initialResult.deadCore);
			final int[] deadCore = LongRunningWrapper.runMethod(method, monitor);
			if (solver.hasTimeoutOccured()) {
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}
			if (deadCore == null) {
				onUpdate.invoke(new ValidationMessage("A problem occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			}
			if (deadCore.length > 0) {
				boolean hasDead = false;
				for (final int f : deadCore) {
					if (f < 0) {
						hasDead = true;
						break;
					}
				}
				if (hasDead) {
					final StringBuilder sb = new StringBuilder("Constraint causes the following features to be dead:\n");
					for (final int f : deadCore) {
						if (f < 0) {
							sb.append(initialResult.satInstance.getVariableObject(f));
							sb.append(", ");
						}
					}
					sb.delete(sb.length() - 2, sb.length());
					onUpdate.invoke(new ValidationMessage(sb.toString(), Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
					return null;
				}
			}

			monitor.checkCancel();
			final List<int[]> possibleFOFeatures =
				LongRunningWrapper.runMethod(new ImplicationAnalysis(solver, initialResult.possibleFOFeatures), monitor.subTask(0));
			if (solver.hasTimeoutOccured()) {
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			}
			if (possibleFOFeatures == null) {
				onUpdate.invoke(new ValidationMessage("A problem occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			}
			if ((possibleFOFeatures != null) && !possibleFOFeatures.isEmpty()) {
				final StringBuilder sb = new StringBuilder("Constraint causes the following features to be false optional:\n");
				for (final int[] is : possibleFOFeatures) {
					sb.append(initialResult.satInstance.getVariableObject(is[1]));
					sb.append(", ");
				}
				sb.delete(sb.length() - 2, sb.length());
				onUpdate.invoke(new ValidationMessage(sb.toString(), Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}

			onUpdate.invoke(new ValidationMessage("Constraint successfully checked.\n", DialogState.SAVE_CHANGES_ENABLED));
			return null;
		}

	}

}
