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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.prop4j.Node;
import org.prop4j.Not;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Nodes;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CoreDeadAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.HasSolutionAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndependentRedundancyAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.CNFCreator;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
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

	public void init(FeatureModelFormula featureModel, IConstraint constraint, final IConsumer<ValidationMessage> onUpdate) {
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
	 * @param constraintNode Test to text
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

			CNF satInstance;
			AdvancedSatSolver solver;

			boolean valid;
			LiteralSet deadCore;
			ClauseList possibleFOFeatures;
		}

		private final FeatureModelFormula featureModel;
		private final IConstraint constraint;

		public InitialAnalysis(FeatureModelFormula featureModel, IConstraint constraint) {
			this.featureModel = featureModel;
			this.constraint = constraint;
		}

		@Override
		public InitialResult execute(IMonitor<InitialResult> monitor) throws Exception {
			monitor.setRemainingWork(3);
			final InitialResult initialResult = new InitialResult();
			CNF cnf = featureModel.getElement(new CNFCreator());
			if (constraint != null) {
				cnf = cnf.clone();
				final ClauseList convert = Nodes.convert(cnf.getVariables(), constraint.getNode());
				final ClauseList clauses = cnf.getClauses();
				for (final LiteralSet constraintLiteralSet : convert) {
					for (final Iterator<LiteralSet> iterator = clauses.iterator(); iterator.hasNext();) {
						final LiteralSet modelLiteralSet = iterator.next();
						if (constraintLiteralSet.equals(modelLiteralSet)) {
							iterator.remove();
							break;
						}
					}
				}
			}
			initialResult.satInstance = cnf;

			initialResult.solver = new AdvancedSatSolver(initialResult.satInstance);
			monitor.step();
			initialResult.valid = null != LongRunningWrapper.runMethod(new HasSolutionAnalysis(initialResult.solver), monitor.subTask(1));

			if (initialResult.valid) {

				monitor.checkCancel();
				initialResult.deadCore = LongRunningWrapper.runMethod(new CoreDeadAnalysis(initialResult.solver), monitor.subTask(1));

				monitor.checkCancel();
				initialResult.possibleFOFeatures = new ClauseList();
				for (final IFeature feature : featureModel.getFeatureModel().getFeatures()) {
					final IFeature parent = FeatureUtils.getParent(feature);
					if ((parent != null) && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
						initialResult.possibleFOFeatures.add(new LiteralSet(-initialResult.satInstance.getVariables().getVariable(parent.getName()),
								initialResult.satInstance.getVariables().getVariable(feature.getName())));
					}
				}

				monitor.checkCancel();
				final List<LiteralSet> foResult =
					LongRunningWrapper.runMethod(new IndependentRedundancyAnalysis(initialResult.solver, initialResult.possibleFOFeatures), monitor.subTask(0));
				if (foResult != null) {
					initialResult.possibleFOFeatures.removeAll(foResult);
				}
			}

			return initialResult;
		}

	}

	private static class Analysis implements LongRunningMethod<Void> {

		private final InitialAnalysis.InitialResult initialResult;
		private final Node constraintNode;
		private final IConsumer<ValidationMessage> onUpdate;

		public Analysis(InitialAnalysis.InitialResult initialResult, Node constraintNode, IConsumer<ValidationMessage> onUpdate) {
			this.initialResult = initialResult;
			this.constraintNode = constraintNode;
			this.onUpdate = onUpdate;
		}

		@Override
		public Void execute(IMonitor<Void> monitor) throws Exception {
			onUpdate.invoke(new ValidationMessage(
					"Checking constraint...\nThis may take a while. Although it is not recommended, you can save the unchecked constraint.",
					DialogState.SAVE_CHANGES_DONT_MIND));

			monitor.checkCancel();
			final CNF constraintCNF = Nodes.convert(constraintNode);
			monitor.checkCancel();
			SatResult satResult = SatResult.FALSE;
			try {
				satResult = new AdvancedSatSolver(constraintCNF).hasSolution();
			} catch (final RuntimeContradictionException e) {}
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
				throw new AssertionError(satResult);
			}

			monitor.checkCancel();
			final CNF reverseConstraintCNF = Nodes.convert(new Not(constraintNode));
			monitor.checkCancel();
			satResult = SatResult.FALSE;
			try {
				satResult = new AdvancedSatSolver(reverseConstraintCNF).hasSolution();
			} catch (final RuntimeContradictionException e) {}
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
				throw new AssertionError(satResult);
			}

			if (!initialResult.valid) {
				onUpdate.invoke(new ValidationMessage("Constraint successfully checked.\n(Feature model is already void)", DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}

			AdvancedSatSolver solver = null;
			monitor.checkCancel();
			satResult = SatResult.FALSE;
			try {
				solver = new AdvancedSatSolver(initialResult.satInstance);
				final ClauseList adaptClauseList = constraintCNF.adaptClauseList(initialResult.satInstance.getVariables());
				if (adaptClauseList != null) {
					solver.addClauses(adaptClauseList);
					satResult = solver.hasSolution();
				} else {
					onUpdate.invoke(
							new ValidationMessage("Constraint contains invalid feature names\n", Problem.Severity.ERROR, DialogState.SAVE_CHANGES_DISABLED));
					return null;
				}
			} catch (final RuntimeContradictionException e) {}
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
				throw new AssertionError(satResult);
			}

			monitor.checkCancel();
			satResult = SatResult.FALSE;
			try {
				final AdvancedSatSolver redundantSolver = new AdvancedSatSolver(initialResult.satInstance);
				final ClauseList adaptClauseList = reverseConstraintCNF.adaptClauseList(initialResult.satInstance.getVariables());
				if (adaptClauseList != null) {
					redundantSolver.addClauses(adaptClauseList);
					satResult = redundantSolver.hasSolution();
				} else {
					onUpdate.invoke(
							new ValidationMessage("Constraint contains invalid feature names\n", Problem.Severity.ERROR, DialogState.SAVE_CHANGES_DISABLED));
					return null;
				}
			} catch (final RuntimeContradictionException e) {}
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
				throw new AssertionError(satResult);
			}

			monitor.checkCancel();
			final CoreDeadAnalysis method = new CoreDeadAnalysis(solver);
			method.setAssumptions(initialResult.deadCore);
			final LiteralSet newDeadCore = LongRunningWrapper.runMethod(method, monitor.subTask(1));
			if (method.isTimeoutOccured()) {
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_ENABLED));
				return null;
			}
			if (newDeadCore == null) {
				onUpdate.invoke(new ValidationMessage("A problem occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			}
			if (!newDeadCore.isEmpty()) {
				boolean hasDead = false;
				for (final int f : newDeadCore.getLiterals()) {
					if (f < 0) {
						hasDead = true;
						break;
					}
				}
				if (hasDead) {
					final StringBuilder sb = new StringBuilder("Constraint causes the following features to be dead:\n");
					for (final int f : newDeadCore.getLiterals()) {
						if (f < 0) {
							sb.append(initialResult.satInstance.getVariables().getName(f));
							sb.append(", ");
						}
					}
					sb.delete(sb.length() - 2, sb.length());
					onUpdate.invoke(new ValidationMessage(sb.toString(), Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
					return null;
				}
			}

			monitor.checkCancel();
			final IndependentRedundancyAnalysis method2 = new IndependentRedundancyAnalysis(solver, initialResult.possibleFOFeatures);
			final List<LiteralSet> possibleFOFeatures = LongRunningWrapper.runMethod(method2, monitor.subTask(0));
			if (method2.isTimeoutOccured()) {
				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			}
			if (possibleFOFeatures == null) {
				onUpdate.invoke(new ValidationMessage("A problem occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
						DialogState.SAVE_CHANGES_DONT_MIND));
				return null;
			}
			final ArrayList<LiteralSet> foFeatures = new ArrayList<>();
			for (final LiteralSet literalSet : possibleFOFeatures) {
				if (literalSet != null) {
					foFeatures.add(literalSet);
				}
			}
			if (!foFeatures.isEmpty()) {
				final StringBuilder sb = new StringBuilder("Constraint causes the following features to be false optional:\n");
				for (final LiteralSet is : foFeatures) {
					sb.append(initialResult.satInstance.getVariables().getName(is.getLiterals()[1]));
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
