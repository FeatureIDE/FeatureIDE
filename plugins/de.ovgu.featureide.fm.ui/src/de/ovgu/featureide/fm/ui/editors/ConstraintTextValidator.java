///* FeatureIDE - A Framework for Feature-Oriented Software Development
// * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
// *
// * This file is part of FeatureIDE.
// *
// * FeatureIDE is free software: you can redistribute it and/or modify
// * it under the terms of the GNU Lesser General Public License as published by
// * the Free Software Foundation, either version 3 of the License, or
// * (at your option) any later version.
// *
// * FeatureIDE is distributed in the hope that it will be useful,
// * but WITHOUT ANY WARRANTY; without even the implied warranty of
// * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// * GNU Lesser General Public License for more details.
// *
// * You should have received a copy of the GNU Lesser General Public License
// * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
// *
// * See http://www.fosd.de/featureide/ for further information.
// */
//package de.ovgu.featureide.fm.ui.editors;
//
//import java.util.ArrayList;
//import java.util.List;
//
//import org.prop4j.Node;
//import org.prop4j.Not;
//import org.prop4j.analyses.ConditionallyCoreDeadAnalysis;
//import org.prop4j.analyses.CoreDeadAnalysis;
//import org.prop4j.analyses.ImplicationAnalysis;
//import org.prop4j.analyses.ValidAnalysis;
//import org.prop4j.solver.BasicSolver;
//import org.prop4j.solver.ISatSolver.SatResult;
//import org.prop4j.solver.SatInstance;
//import org.sat4j.specs.ContradictionException;
//
//import de.ovgu.featureide.fm.core.FeatureComparator;
//import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
//import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
//import de.ovgu.featureide.fm.core.base.FeatureUtils;
//import de.ovgu.featureide.fm.core.base.IConstraint;
//import de.ovgu.featureide.fm.core.base.IFeature;
//import de.ovgu.featureide.fm.core.base.IFeatureModel;
//import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
//import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
//import de.ovgu.featureide.fm.core.functional.Functional;
//import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
//import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
//import de.ovgu.featureide.fm.ui.FMUIPlugin;
//import de.ovgu.featureide.fm.core.io.Problem;
//import de.ovgu.featureide.fm.core.job.IJob;
//import de.ovgu.featureide.fm.core.job.IJob.JobStatus;
//import de.ovgu.featureide.fm.core.job.IRunner;
//import de.ovgu.featureide.fm.core.job.JobStartingStrategy;
//import de.ovgu.featureide.fm.core.job.JobToken;
//import de.ovgu.featureide.fm.core.job.LongRunningMethod;
//import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
//import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
//import de.ovgu.featureide.fm.core.job.util.JobFinishListener;
//import de.ovgu.featureide.fm.ui.editors.ConstraintDialog.DialogState;
//import de.ovgu.featureide.fm.ui.editors.ConstraintDialog.ValidationMessage;
//
///**
// * Class which contains several tests for {@link ConstraintDialog} text field, which contains user written constraints.
// *
// * @author Marcus Pinnecke
// */
//public final class ConstraintTextValidator {
//
//	private InitialAnalysis.InitialResult initialResult;
//	private JobToken initToken;
//	private JobToken token;
//
//<<<<<<< HEAD
//		final NodeReader nodeReader = new NodeReader();
//
//		final Node propNode = nodeReader.stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(clonedModel.getFeatures())));
//
//		if (propNode != null) {
//			if (constraint != null) {
//				clonedModel.removeConstraint(constraint);
//			}
//			deadFeaturesBefore = FeatureModelManager.getAnalyzer(clonedModel).getDeadFeatures();
//			clonedModel.addConstraint(new Constraint(clonedModel, propNode));
//			clonedModel.handleModelDataChanged();
//		}
//
//		final SortedSet<IFeature> deadFeaturesAfter = new TreeSet<IFeature>(new FeatureComparator(true));
//
//		for (final IFeature l : FeatureModelManager.getAnalyzer(clonedModel).getDeadFeatures()) {
//			if (!deadFeaturesBefore.contains(l)) {
//				deadFeaturesAfter.add(l);
//
//			}
//		}
//		return deadFeaturesAfter;
//	}
//
//	/**
//	 * returns a String to be displayed in the dialog header contains the list of dead features
//	 *
//	 * @param deadFeatures List of dead Features
//	 **/
//	private String getDeadFeatureString(Set<IFeature> deadFeatures) {
//		final StringBuilder featureString = new StringBuilder();
//		featureString.append("Constraint causes the following features to be dead: ");
//		int count = 0;
//		int featureCount = 0;
//		boolean isNewLine = false;
//		for (final IFeature l : deadFeatures) {
//			count = count + l.toString().length() + 2;
//
//			if ((isNewLine == false) && (count > 35)) {
//				featureString.append('\n');
//				isNewLine = true;
//			}
//			if (count < 90) {
//				featureString.append(l.getName());
//				if (featureCount < (deadFeatures.size() - 1)) {
//					featureString.append(", ");
//=======
//	public void init(IFeatureModel featureModel, IConstraint constraint, final IConsumer<ValidationMessage> onUpdate) {
//		initToken = LongRunningWrapper.createToken(JobStartingStrategy.RETURN);
//		token = LongRunningWrapper.createToken(JobStartingStrategy.CANCEL_WAIT_ONE);
//		final IRunner<InitialAnalysis.InitialResult> runner = LongRunningWrapper.getRunner(new InitialAnalysis(featureModel, constraint));
//		runner.addJobFinishedListener(new JobFinishListener<InitialAnalysis.InitialResult>() {
//			@Override
//			public void jobFinished(IJob<InitialAnalysis.InitialResult> finishedJob) {
//				final ValidationMessage m = new ValidationMessage("");
//				if (finishedJob.getStatus() == JobStatus.OK) {
//					initialResult = finishedJob.getResults();
//					m.setInitialAnalysisSuccess(true);
//				} else {
//					m.setInitialAnalysisSuccess(false);
//>>>>>>> refs/remotes/origin/issue_793
//				}
//				onUpdate.invoke(m);
//			}
//		});
//		onUpdate.invoke(new ValidationMessage(
//				"Executing initial analysis...\nThis may take a while. Although it is not recommended, you can save the unchecked constraint."));
//		LongRunningWrapper.startJob(initToken, runner);
//	}
//<<<<<<< HEAD
//
//	private List<IFeature> getFalseOptional(IConstraint constraint, String input, IFeatureModel model) {
//		final List<IFeature> list = new ArrayList<IFeature>();
//		final IFeatureModel clonedModel = model.clone(null);
//
//		final NodeReader nodeReader = new NodeReader();
//
//		final Node propNode = nodeReader.stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(clonedModel.getFeatures())));
//
//		// The following code fixes issue #406; should be enhanced in further development
//		// to not always clone the whole feature model for every performed analysis
//		if (propNode != null) {
//			if (constraint != null) {
//				clonedModel.removeConstraint(constraint);
//			}
//		}
//
//		for (final IFeature feature : model.getFeatures()) {
//			if (input.contains(feature.getName())) {
//				clonedModel.addConstraint(new Constraint(clonedModel, propNode));
//			}
//		}
//		final FeatureModelAnalyzer analyzer = FeatureModelManager.getAnalyzer(clonedModel);
//		analyzer.analyzeFeatureModel(null);
//
//		for (final IFeature feature : model.getFeatures()) {
//			if (input.contains(feature.getName())) {
//				if (analyzer.getFeatureProperties(feature).hasStatus(FeatureStatus.FALSE_OPTIONAL) && !list.contains(feature)) {
//					list.add(feature);
//				}
//			}
//		}
//
//		return list;
//	}
//
//	private String getFalseOptionalString(List<IFeature> list) {
//		final String listString = Functional.join(list, ",", FeatureUtils.GET_FEATURE_NAME);
//		final String featureString = "Constraint causes the following features to be false optional: " + '\n';
//		return featureString + listString;
//	}
//
//	/**
//	 * Tests if the {@link IConstraint} will change the product line.
//	 *
//	 * @param constraint The actual {@link IConstraint}
//	 * @return <code>true</code> if the {@link IConstraint} is redundant
//	 */
//	private boolean isRedundant(IConstraint constraint, final IFeatureModel featureModel, String input, final int timeOut) {
//		if (input.length() == 0) {
//			return false;
//		}
//		final IFeatureModel clonedModel = featureModel.clone(null);
//		final Node propNode = new NodeReader().stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(clonedModel.getFeatures())));
//
//		// The following code fixes issue #406; should be enhanced in further development
//		// to not always clone the whole feature model for every performed analysis
//		if (propNode != null) {
//			if (constraint != null) {
//				clonedModel.removeConstraint(constraint);
//			}
//		}
//
//		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(clonedModel);
//		final Node check = new Implies(nodeCreator.createNodes(), propNode);
//
//		final SatSolver satsolver = new SatSolver(new Not(check), timeOut);
//
//		try {
//			return !satsolver.hasSolution();
//		} catch (final TimeoutException e) {
//			return true;
//		}
//	}
//
//	/**
//	 * returns true if constraint is satisfiable otherwise false
//	 *
//	 * @param constraint the constraint to be evaluated
//	 * @param timeout timeout in ms
//	 */
//	public static boolean isSatisfiable(String constraint, int timeout) {
//		final NodeReader nodeReader = new NodeReader();
//		final SatSolver satsolver = new SatSolver(nodeReader.stringToNode(constraint).clone(), timeout);
//		try {
//			return satsolver.hasSolution();
//		} catch (final TimeoutException e) {
//			FMUIPlugin.getDefault().logError(e);
//			return true;
//		}
//
//	}
//
//	/**
//	 * returns true if the constraint is always true
//	 *
//	 * @param constraint the constraint to be evaluated
//	 * @param timeout timeout in ms
//	 *
//	 */
//	private boolean isTautology(String constraint, int timeout) {
//		final NodeReader nodeReader = new NodeReader();
//		final Node node = nodeReader.stringToNode(constraint);
//
//		final SatSolver satsolver = new SatSolver(new Not(node.clone()), timeout);
//
//		try {
//			return !satsolver.hasSolution();
//		} catch (final TimeoutException e) {
//			return true;
//		}
//
//	}
//
//	/**
//	 * Data class
//	 *
//	 * @author Marcus Pinnecke
//	 */
//	public static class ValidationMessage {
//
//		final ValidationResult validationResult;
//		final String details;
//
//		public ValidationMessage() {
//			this(ValidationResult.OK, "");
//		}
//
//		public ValidationMessage(ValidationResult result) {
//			this(result, "");
//		}
//
//		public ValidationMessage(ValidationResult result, String message) {
//			validationResult = result;
//			details = message;
//		}
//	}
//
//	/**
//	 * Return value for several validation tests.
//	 *
//	 * @author Marcus Pinnecke
//	 */
//	public enum ValidationResult {
//		OK, NOT_WELLFORMED, IS_TAUTOLOGY, IS_NOT_SATISFIABLE, VOIDS_MODEL, FALSE_OPTIONAL_FEATURE, DEAD_FEATURE, REDUNDANT
//	}
//
//	private ValidationJob asyncCheckJob = null;
//=======
//>>>>>>> refs/remotes/origin/issue_793
//
//	public void cancelValidation() {
//		LongRunningWrapper.cancelAllJobs(token);
//		LongRunningWrapper.cancelAllJobs(initToken);
//	}
//
//	/**
//	 * Runs tests not blocking the current GUI thread. The result will be returned each test's result and a separate notification before the first tests starts
//	 * and (in case of all test has passed) when the entire series has ended.
//	 *
//	 * @param constraintNode Test to text
//	 * @param onUpdate Update mechanism
//	 */
//<<<<<<< HEAD
//	public void validateAsync(final IConstraint constraint, final int timeOut, final IFeatureModel featureModel, final String constraintText,
//			final IConsumer<ValidationMessage> onCheckStarted, final IConsumer<ValidationMessage> onVoidsModelCheckComplete,
//			final IConsumer<ValidationMessage> onFalseOptionalCheckComplete, final IConsumer<ValidationMessage> onDeadFeatureCheckComplete,
//			final IConsumer<ValidationMessage> onIsRedundantCheckComplete, final IConsumer<ValidationMessage> onCheckEnded,
//			final IConsumer<ValidationMessage> onIsTautology, final IConsumer<ValidationMessage> onIsNotSatisfiable) {
//
//		final String con = constraintText.trim();
//
//		cancelValidation();
//
//		asyncCheckJob = new ValidationJob(RUNNING_ADDITIONAL_CHECKS___) {
//
//			@Override
//			protected IStatus run(IProgressMonitor monitor) {
//
//				updateUI(onCheckStarted, "");
//				// ---------------------------------------------------------
//				if (!canceled) {
//					final boolean problemFoundTautology = isTautology(con, timeOut);
//
//					if (problemFoundTautology) {
//						updateUI(onIsTautology, "");
//						return Status.OK_STATUS;
//					}
//				}
//
//				// ---------------------------------------------------------
//				if (!canceled) {
//					final boolean problemFoundNotSatisfiable = !isSatisfiable(con, timeOut);
//
//					if (problemFoundNotSatisfiable) {
//						updateUI(onIsNotSatisfiable, "");
//						return Status.OK_STATUS;
//					}
//				}
//				// ---------------------------------------------------------
//				if (!canceled) {
//					final boolean problemFoundVoidsModel = isVoidsModel(featureModel, con, constraint);
//
//					if (problemFoundVoidsModel) {
//						updateUI(onVoidsModelCheckComplete, "");
//						return Status.OK_STATUS;
//					}
//				}
//				// ---------------------------------------------------------
//				if (!canceled) {
//					final List<IFeature> falseOptionalFeatures = getFalseOptional(constraint, con, featureModel);
//
//					if (!falseOptionalFeatures.isEmpty()) {
//						updateUI(onFalseOptionalCheckComplete, getFalseOptionalString(falseOptionalFeatures));
//						return Status.OK_STATUS;
//					}
//				}
//				// ---------------------------------------------------------
//				if (!canceled) {
//					final Set<IFeature> deadFeatuers = getDeadFeatures(constraint, con, featureModel);
//
//					if (!deadFeatuers.isEmpty()) {
//						updateUI(onDeadFeatureCheckComplete, getDeadFeatureString(deadFeatuers));
//						return Status.OK_STATUS;
//					}
//				}
//				// ---------------------------------------------------------
//				if (!canceled) {
//					final boolean problemFoundRedundant = isRedundant(constraint, featureModel, con, timeOut);
//
//					if (problemFoundRedundant) {
//						updateUI(onIsRedundantCheckComplete, "");
//						return Status.OK_STATUS;
//					}
//				}
//				// ---------------------------------------------------------
//				if (!canceled) {
//					updateUI(onCheckEnded, "");
//				}
//
//				return Status.OK_STATUS;
//			}
//
//			private void updateUI(final IConsumer<ValidationMessage> consumer, final String message) {
//				if (!canceled) {
//					new UIJob("Updating ConstraintDialog Message") {
//
//						@Override
//						public IStatus runInUIThread(IProgressMonitor monitor) {
//							if (!canceled) {
//								consumer.invoke(new ValidationMessage(null, message));
//							}
//							return Status.OK_STATUS;
//						}
//					}.schedule();
//				}
//			}
//
//		};
//		asyncCheckJob.setPriority(Job.DECORATE);
//		asyncCheckJob.setSystem(true);
//		asyncCheckJob.schedule();
//	}
//
//	/**
//	 * @throws MakesModelVoidValidatorException
//	 *
//	 */
//	private boolean isVoidsModel(IFeatureModel featureModel, String con, IConstraint constraint) {
//		try {
//			return voidsModel(constraint, con, featureModel);
//		} catch (final TimeoutException e) {
//			FMUIPlugin.getDefault().logError(e);
//		}
//		return false;
//	}
//
//	/**
//	 * returns true if the constraint causes the feature model to be void otherwise false
//	 *
//	 * @param input constraint to be evaluated
//	 * @param model the feature model
//	 *
//	 *        * @throws TimeoutException
//	 */
//	private boolean voidsModel(final IConstraint constraint, String input, IFeatureModel model) throws TimeoutException {
//		if (!FeatureModelManager.getAnalyzer(model).isValid()) {
//
//=======
//	public boolean validateAsync(final Node constraintNode, final IConsumer<ValidationMessage> onUpdate) {
//		if (initialResult != null) {
//			LongRunningWrapper.startJob(token, LongRunningWrapper.getRunner(new Analysis(initialResult, constraintNode, onUpdate)));
//			return true;
//		} else {
//>>>>>>> refs/remotes/origin/issue_793
//			return false;
//		}
//	}
//
//	private static class InitialAnalysis implements LongRunningMethod<InitialAnalysis.InitialResult> {
//
//		private static class InitialResult {
//			SatInstance satInstance;
//			BasicSolver solver;
//
//			boolean valid;
//			int[] deadCore;
//			List<int[]> possibleFOFeatures;
//		}
//
//		private final IFeatureModel featureModel;
//		private final IConstraint constraint;
//
//		public InitialAnalysis(IFeatureModel featureModel, IConstraint constraint) {
//			this.featureModel = featureModel;
//			this.constraint = constraint;
//		}
//
//		@Override
//		public InitialResult execute(IMonitor monitor) throws Exception {
//			final InitialResult initialResult = new InitialResult();
//			final IFeatureModel clone = featureModel.clone();
//			if (constraint != null) {
//				clone.removeConstraint(constraint);
//			}
//			final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(clone);
//			nodeCreator.setCnfType(CNFType.Regular);
//			nodeCreator.setIncludeBooleanValues(false);
//			initialResult.satInstance = new SatInstance(nodeCreator.createNodes(), Functional.toList(FeatureUtils.getFeatureNamesList(clone)));
//
//			initialResult.valid = true;
//			try {
//				initialResult.solver = new BasicSolver(initialResult.satInstance);
//				monitor.checkCancel();
//				initialResult.valid = null != LongRunningWrapper.runMethod(new ValidAnalysis(initialResult.solver), monitor);
//			} catch (final ContradictionException contraExc) {
//				initialResult.valid = false;
//			}
//
//			if (initialResult.valid) {
//
//				monitor.checkCancel();
//				final int[] deadCoreResult = LongRunningWrapper.runMethod(new CoreDeadAnalysis(initialResult.solver), monitor);
//				initialResult.deadCore = deadCoreResult == null ? new int[0] : deadCoreResult;
//
//				monitor.checkCancel();
//				initialResult.possibleFOFeatures = new ArrayList<>();
//				for (final IFeature feature : clone.getFeatures()) {
//					final IFeature parent = FeatureUtils.getParent(feature);
//					if ((parent != null) && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
//						initialResult.possibleFOFeatures.add(new int[] { -initialResult.satInstance.getVariable(parent.getName()),
//							initialResult.satInstance.getVariable(feature.getName()) });
//					}
//				}
//
//				monitor.checkCancel();
//				final List<int[]> foResult =
//					LongRunningWrapper.runMethod(new ImplicationAnalysis(initialResult.solver, initialResult.possibleFOFeatures), monitor.subTask(0));
//				if (foResult != null) {
//					initialResult.possibleFOFeatures.removeAll(foResult);
//				}
//			}
//
//			return initialResult;
//		}
//
//<<<<<<< HEAD
//		return (!FeatureModelManager.getAnalyzer(clonedModel).isValid());
//=======
//	}
//
//	private static class Analysis implements LongRunningMethod<Void> {
//
//		private final InitialAnalysis.InitialResult initialResult;
//		private Node constraintNode;
//		private final IConsumer<ValidationMessage> onUpdate;
//
//		public Analysis(InitialAnalysis.InitialResult initialResult, Node constraintNode, IConsumer<ValidationMessage> onUpdate) {
//			this.initialResult = initialResult;
//			this.constraintNode = constraintNode;
//			this.onUpdate = onUpdate;
//		}
//
//		@Override
//		public Void execute(IMonitor monitor) throws Exception {
//			onUpdate.invoke(new ValidationMessage(
//					"Checking constraint...\nThis may take a while. Although it is not recommended, you can save the unchecked constraint.",
//					DialogState.SAVE_CHANGES_DONT_MIND));
//
//			monitor.checkCancel();
//			constraintNode = constraintNode.toRegularCNF();
//
//			monitor.checkCancel();
//			BasicSolver solver;
//			try {
//				solver = new BasicSolver(new SatInstance(constraintNode));
//			} catch (final ContradictionException e) {
//				onUpdate.invoke(new ValidationMessage("Constraint is a contradiction\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			}
//			SatResult satResult = solver.isSatisfiable();
//			switch (satResult) {
//			case FALSE:
//				onUpdate.invoke(new ValidationMessage("Constraint is a contradiction\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			case TIMEOUT:
//				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_DONT_MIND));
//				return null;
//			case TRUE:
//				break;
//			default:
//				break;
//			}
//
//			monitor.checkCancel();
//			final Node inverseNode = new Not(constraintNode.clone()).toRegularCNF();
//			try {
//				solver = new BasicSolver(new SatInstance(inverseNode));
//			} catch (final ContradictionException e) {
//				onUpdate.invoke(new ValidationMessage("Constraint is a tautology\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			}
//			satResult = solver.isSatisfiable();
//			switch (satResult) {
//			case FALSE:
//				onUpdate.invoke(new ValidationMessage("Constraint is a tautology\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			case TIMEOUT:
//				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_DONT_MIND));
//				return null;
//			case TRUE:
//				break;
//			default:
//				break;
//			}
//
//			if (!initialResult.valid) {
//				onUpdate.invoke(new ValidationMessage("Constraint successfully checked.\n(Feature model is already void)", DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			}
//
//			monitor.checkCancel();
//			solver = new BasicSolver(initialResult.satInstance);
//			try {
//				solver.addClauses(constraintNode);
//			} catch (final ContradictionException e) {
//				onUpdate.invoke(
//						new ValidationMessage("Constraint causes the feature model to be void\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			}
//			satResult = solver.isSatisfiable();
//			switch (satResult) {
//			case FALSE:
//				onUpdate.invoke(
//						new ValidationMessage("Constraint causes the feature model to be void\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			case TIMEOUT:
//				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_DONT_MIND));
//				return null;
//			case TRUE:
//				break;
//			default:
//				break;
//			}
//
//			monitor.checkCancel();
//			final BasicSolver inverseSolver = new BasicSolver(initialResult.satInstance);
//			try {
//				inverseSolver.addClauses(inverseNode);
//			} catch (final ContradictionException e) {
//				onUpdate.invoke(new ValidationMessage("Constraint is redundant\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			}
//			satResult = inverseSolver.isSatisfiable();
//			switch (satResult) {
//			case FALSE:
//				onUpdate.invoke(new ValidationMessage("Constraint is redundant\n", Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			case TIMEOUT:
//				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_DONT_MIND));
//				return null;
//			case TRUE:
//				break;
//			default:
//				break;
//			}
//
//			monitor.checkCancel();
//			final ConditionallyCoreDeadAnalysis method = new ConditionallyCoreDeadAnalysis(solver);
//			method.setAssumptions(initialResult.deadCore);
//			final int[] deadCore = LongRunningWrapper.runMethod(method, monitor);
//			if (solver.hasTimeoutOccured()) {
//				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			}
//			if (deadCore == null) {
//				onUpdate.invoke(new ValidationMessage("A problem occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_DONT_MIND));
//				return null;
//			}
//			if (deadCore.length > 0) {
//				boolean hasDead = false;
//				for (final int f : deadCore) {
//					if (f < 0) {
//						hasDead = true;
//						break;
//					}
//				}
//				if (hasDead) {
//					final StringBuilder sb = new StringBuilder("Constraint causes the following features to be dead:\n");
//					for (final int f : deadCore) {
//						if (f < 0) {
//							sb.append(initialResult.satInstance.getVariableObject(f));
//							sb.append(", ");
//						}
//					}
//					sb.delete(sb.length() - 2, sb.length());
//					onUpdate.invoke(new ValidationMessage(sb.toString(), Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//					return null;
//				}
//			}
//
//			monitor.checkCancel();
//			final List<int[]> possibleFOFeatures =
//				LongRunningWrapper.runMethod(new ImplicationAnalysis(solver, initialResult.possibleFOFeatures), monitor.subTask(0));
//			if (solver.hasTimeoutOccured()) {
//				onUpdate.invoke(new ValidationMessage("A timeout occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_DONT_MIND));
//				return null;
//			}
//			if (possibleFOFeatures == null) {
//				onUpdate.invoke(new ValidationMessage("A problem occured - Constraint could not be checked completely\n", Problem.Severity.WARNING,
//						DialogState.SAVE_CHANGES_DONT_MIND));
//				return null;
//			}
//			if ((possibleFOFeatures != null) && !possibleFOFeatures.isEmpty()) {
//				final StringBuilder sb = new StringBuilder("Constraint causes the following features to be false optional:\n");
//				for (final int[] is : possibleFOFeatures) {
//					sb.append(initialResult.satInstance.getVariableObject(is[1]));
//					sb.append(", ");
//				}
//				sb.delete(sb.length() - 2, sb.length());
//				onUpdate.invoke(new ValidationMessage(sb.toString(), Problem.Severity.WARNING, DialogState.SAVE_CHANGES_ENABLED));
//				return null;
//			}
//
//			onUpdate.invoke(new ValidationMessage("Constraint successfully checked.\n", DialogState.SAVE_CHANGES_ENABLED));
//			return null;
//		}
//>>>>>>> refs/remotes/origin/issue_793
//
//	}
//
//}

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
		public InitialResult execute(IMonitor monitor) throws Exception {
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
			monitor.checkCancel();
			initialResult.valid = null != LongRunningWrapper.runMethod(new HasSolutionAnalysis(initialResult.solver), monitor);

			if (initialResult.valid) {

				monitor.checkCancel();
				initialResult.deadCore = LongRunningWrapper.runMethod(new CoreDeadAnalysis(initialResult.solver), monitor);

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
		public Void execute(IMonitor monitor) throws Exception {
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
				solver.addClauses(constraintCNF.adapt(initialResult.satInstance.getVariables()));
				satResult = solver.hasSolution();
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
				redundantSolver.addClauses(reverseConstraintCNF.adapt(initialResult.satInstance.getVariables()));
				satResult = redundantSolver.hasSolution();
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
			final LiteralSet newDeadCore = LongRunningWrapper.runMethod(method, monitor);
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
			if ((possibleFOFeatures != null) && !possibleFOFeatures.isEmpty()) {
				final StringBuilder sb = new StringBuilder("Constraint causes the following features to be false optional:\n");
				for (final LiteralSet is : possibleFOFeatures) {
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
