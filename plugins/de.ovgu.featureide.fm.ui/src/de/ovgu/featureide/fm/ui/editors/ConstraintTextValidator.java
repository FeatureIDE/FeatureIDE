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
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.ui.progress.UIJob;
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.FunctionalInterfaces.IConsumer;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Class which contains several tests for {@link ConstraintDialog} text field,
 * which contains user written constraints.
 * 
 * @author Marcus Pinnecke
 */
public final class ConstraintTextValidator {

	/**
	 * returns a List of all features that are caused to be dead by the
	 * constraint input
	 * 
	 * @param input
	 *            constraint to be evaluated
	 * @param model
	 *            the feature model
	 * @return List of all dead Features, empty if no feature is caused to be
	 *         dead
	 */
	private SortedSet<Feature> getDeadFeatures(Constraint constraint, String input, FeatureModel model) {
		Collection<Feature> deadFeaturesBefore = null;
		FeatureModel clonedModel = model.clone();

		NodeReader nodeReader = new NodeReader();

		Node propNode = nodeReader.stringToNode(input, clonedModel.getFeatureNames());

		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removeConstraint(constraint);
			}
			deadFeaturesBefore = clonedModel.getAnalyser().getDeadFeatures();
			clonedModel.addPropositionalNode(propNode);
			clonedModel.handleModelDataChanged();
		}

		final SortedSet<Feature> deadFeaturesAfter = new TreeSet<Feature>(new FeatureComparator(true));

		for (Feature l : clonedModel.getAnalyser().getDeadFeatures()) {
			if (!deadFeaturesBefore.contains(l)) {
				deadFeaturesAfter.add(l);

			}
		}
		return deadFeaturesAfter;
	}

	/**
	 * returns a String to be displayed in the dialog header contains the list
	 * of dead features
	 * 
	 * @param deadFeatures
	 *            List of dead Features
	 **/
	private String getDeadFeatureString(Set<Feature> deadFeatures) {
		StringBuilder featureString = new StringBuilder();
		featureString.append("Constraint causes the following features to be dead: ");
		int count = 0;
		int featureCount = 0;
		boolean isNewLine = false;
		for (Feature l : deadFeatures) {
			count = count + l.toString().length() + 2;

			if (isNewLine == false && count > 35) {
				featureString.append('\n');
				isNewLine = true;
			}
			if (count < 90) {
				featureString.append(l);
				if (featureCount < deadFeatures.size() - 1)
					featureString.append(", ");
				featureCount++;

			}

		}
		if (featureCount < deadFeatures.size()) {
			featureString.append("...");
		}
		return featureString.toString();
	}

	private List<Feature> getFalseOptional(String input, FeatureModel model) {
		List<Feature> list = new ArrayList<Feature>();
		FeatureModel clonedModel = model.clone();

		NodeReader nodeReader = new NodeReader();

		Node propNode = nodeReader.stringToNode(input, clonedModel.getFeatureNames());

		for (Feature feature : model.getFeatures()) {
			if (input.contains(feature.getName())) {
				//if (feature.getFeatureStatus() != FeatureStatus.FALSE_OPTIONAL) {
				clonedModel.addPropositionalNode(propNode);
				clonedModel.getAnalyser().analyzeFeatureModel(null);
				if (clonedModel.getFeature(feature.getName()).getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL && !list.contains(feature))
					list.add(feature);
				//}
			}
		}

		return list;
	}

	private String getFalseOptionalString(List<Feature> list) {
		String listString = list.toString();
		String featureString = "Constraint causes the following features to be false optional: " + '\n';
		return featureString + listString.substring(1, listString.length() - 1);
	}

	/**
	 * Tests if the {@link Constraint} will change the product line.
	 * 
	 * @param constraint
	 *            The actual {@link Constraint}
	 * @return <code>true</code> if the {@link Constraint} is redundant
	 */
	private boolean isRedundant(final FeatureModel featureModel, String constraint) {
		if (constraint.length() == 0) {
			return false;
		}
		FeatureModel clonedModel = featureModel.clone();
		Node propNode = new NodeReader().stringToNode(constraint, clonedModel.getFeatureNames());
		clonedModel.addPropositionalNode(propNode);
		if (new ModelComparator(20000).compare(featureModel, clonedModel) == Comparison.REFACTORING) {
			return true;
		}
		return false;
	}

	/**
	 * returns true if constraint is satisfiable otherwise false
	 * 
	 * @param constraint
	 *            the constraint to be evaluated
	 * @param timeout
	 *            timeout in ms
	 */
	public static boolean isSatisfiable(String constraint, int timeout) {
		NodeReader nodeReader = new NodeReader();
		SatSolver satsolver = new SatSolver(nodeReader.stringToNode(constraint).clone(), timeout);
		try {
			return satsolver.isSatisfiable();
		} catch (TimeoutException e) {
			FMUIPlugin.getDefault().logError(e);
			return true;
		}

	}

	/**
	 * returns true if the constraint is always true
	 * 
	 * @param constraint
	 *            the constraint to be evaluated
	 * @param timeout
	 *            timeout in ms
	 * 
	 */
	private boolean isTautology(String constraint, int timeout) {
		NodeReader nodeReader = new NodeReader();
		Node node = nodeReader.stringToNode(constraint);

		SatSolver satsolver = new SatSolver(new Not(node.clone()), timeout);

		try {
			return !satsolver.isSatisfiable();
		} catch (TimeoutException e) {

			return true;
		}

	}

	/**
	 * Data class
	 * 
	 * @author Marcus Pinnecke
	 */
	public static class ValidationMessage {
		final ValidationResult validationResult;
		final String details;

		public ValidationMessage() {
			this(ValidationResult.OK, "");
		}

		public ValidationMessage(ValidationResult result) {
			this(result, "");
		}

		public ValidationMessage(ValidationResult result, String message) {
			this.validationResult = result;
			this.details = message;
		}
	}

	/**
	 * Return value for several validation tests.
	 * 
	 * @author Marcus Pinnecke
	 */
	public enum ValidationResult {
		OK, NOT_WELLFORMED, IS_TAUTOLOGY, IS_NOT_SATISFIABLE, VOIDS_MODEL, FALSE_OPTIONAL_FEATURE, DEAD_FEATURE, REDUNDANT
	}

	/**
	 * Runs tests blocking the current GUI thread. The result will be returned immediately. It will return
	 * ValidationResult.NOT_WELLFORMED if the constraint text is not well formed nad ValidationResult.OK otherwise.
	 * 
	 * @param featureModel Feature model
	 * @param constraintText Text which should be validated
	 * @return
	 */
	public ValidationResult validateSync(final FeatureModel featureModel, final String constraintText) {

		final String con = constraintText.trim();

		if (!isWellformed(featureModel, con))
			return ValidationResult.NOT_WELLFORMED;

		return ValidationResult.OK;
	}

	private ValidationJob asyncCheckJob = null;

	public void cancelValidation() {
		if (asyncCheckJob != null) {
			asyncCheckJob.cancel();
			asyncCheckJob = null;
		}
	}

	public abstract class ValidationJob extends Job {
		public ValidationJob(String name) {
			super(name);
		}

		protected volatile boolean canceled = false;

		@Override
		protected void canceling() {
			this.canceled = true;
		}
	}

	/**
	 * Runs tests not blocking the current GUI thread. The result will be returned each test's result and a separate notification
	 * before the first tests starts and (in case of all test has passed) when the entire series has ended.
	 * 
	 * @param constraint Constraint
	 * @param timeOut Timeout
	 * @param featureModel FeatureModel
	 * @param constraintText Test to text
	 * @param onCheckStarted Observer, before the first test runs.
	 * @param onVoidsModelCheckComplete Observer, when there is a result for "voids model" test
	 * @param onFalseOptionalCheckComplete Observer, when there is a result for "false optional" test
	 * @param onDeadFeatureCheckComplete Observer, when there is a result for "dead feature" test
	 * @param onIsRedundantCheckComplete Observer, when there is a result for "redundant check" test
	 * @param onIsTautology Observer, when there is a result for "tautology" test
	 * @param onIsNotSatisfiable Observer, when there is a result for "is satisfiable" test
	 * @param onCheckEnded Observer, when the entire series has passed and ended
	 */
	public void validateAsync(final Constraint constraint, final int timeOut, final FeatureModel featureModel, final String constraintText,
			final IConsumer<ValidationMessage> onCheckStarted, final IConsumer<ValidationMessage> onVoidsModelCheckComplete,
			final IConsumer<ValidationMessage> onFalseOptionalCheckComplete, final IConsumer<ValidationMessage> onDeadFeatureCheckComplete,
			final IConsumer<ValidationMessage> onIsRedundantCheckComplete, final IConsumer<ValidationMessage> onCheckEnded,
			final IConsumer<ValidationMessage> onIsTautology, final IConsumer<ValidationMessage> onIsNotSatisfiable) {

		final String con = constraintText.trim();

		this.cancelValidation();

		asyncCheckJob = new ValidationJob("Running additional checks...") {

			protected IStatus run(IProgressMonitor monitor) {

				new UIJob("Starting up...") {

					@Override
					public IStatus runInUIThread(IProgressMonitor monitor) {
						if (!canceled) {
							onCheckStarted.invoke(new ValidationMessage());
						}
						return Status.OK_STATUS;
					}

				}.schedule();
				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundTautology = isTautology(con, timeOut);

					new UIJob("Updating results tautology check...") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								onIsTautology.invoke(new ValidationMessage(!problemFoundTautology ? ValidationResult.OK : ValidationResult.IS_TAUTOLOGY));
							}
							return Status.OK_STATUS;
						}

					}.schedule();

					if (problemFoundTautology)
						return Status.OK_STATUS;
				}

				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundNotSatisfiable = !isSatisfiable(con, timeOut);

					new UIJob("Updating results for satisfiable check...") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								onIsNotSatisfiable.invoke(new ValidationMessage(!problemFoundNotSatisfiable ? ValidationResult.OK
										: ValidationResult.IS_NOT_SATISFIABLE));
							}
							return Status.OK_STATUS;
						}
					}.schedule();

					if (problemFoundNotSatisfiable)
						return Status.OK_STATUS;
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundVoidsModel = isVoidsModel(featureModel, con, constraint);

					new UIJob("Updating results for voids model...") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								onVoidsModelCheckComplete.invoke(new ValidationMessage(!problemFoundVoidsModel ? ValidationResult.OK
										: ValidationResult.VOIDS_MODEL));
							}
							return Status.OK_STATUS;
						}
					}.schedule();

					if (problemFoundVoidsModel)
						return Status.OK_STATUS;
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final List<Feature> falseOptionalFeatures = getFalseOptional(con, featureModel);

					new UIJob("Updating results for false optional features...") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								onFalseOptionalCheckComplete.invoke(new ValidationMessage(falseOptionalFeatures.isEmpty() ? ValidationResult.OK
										: ValidationResult.FALSE_OPTIONAL_FEATURE, getFalseOptionalString(falseOptionalFeatures)));
							}
							return Status.OK_STATUS;
						}
					}.schedule();

					if (!falseOptionalFeatures.isEmpty())
						return Status.OK_STATUS;
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final Set<Feature> deadFeatuers = getDeadFeatures(constraint, con, featureModel);

					new UIJob("Updating results for dead features...") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								onDeadFeatureCheckComplete.invoke(new ValidationMessage(deadFeatuers.isEmpty() ? ValidationResult.OK
										: ValidationResult.FALSE_OPTIONAL_FEATURE, getDeadFeatureString(deadFeatuers)));
							}
							return Status.OK_STATUS;
						}
					}.schedule();

					if (!deadFeatuers.isEmpty())
						return Status.OK_STATUS;
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundRedundant = isRedundant(featureModel, con);

					new UIJob("Updating results for redundancy...") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								onIsRedundantCheckComplete.invoke(new ValidationMessage(!problemFoundRedundant ? ValidationResult.OK
										: ValidationResult.FALSE_OPTIONAL_FEATURE, ""));
							}
							return Status.OK_STATUS;
						}
					}.schedule();

					if (problemFoundRedundant)
						return Status.OK_STATUS;
				}
				// ---------------------------------------------------------
				if (!canceled) {
					new UIJob("Checking complete.") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								onCheckEnded.invoke(new ValidationMessage());
							}
							return Status.OK_STATUS;
						}
					}.schedule();
				}

				return Status.OK_STATUS;
			}

		};
		asyncCheckJob.setPriority(Job.DECORATE);
		asyncCheckJob.setSystem(true);
		asyncCheckJob.schedule();
	}

	/**
	 * @throws MakesModelVoidValidatorException
	 * 
	 */
	private boolean isVoidsModel(FeatureModel featureModel, String con, Constraint constraint) {
		try {
			return voidsModel(constraint, con, featureModel);
		} catch (TimeoutException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * @throws SyntaxErrorValidatorException
	 * 
	 */
	private boolean isWellformed(FeatureModel featureModel, String con) {
		NodeReader nodereader = new NodeReader();
		boolean isWellformed = nodereader.isWellFormed(con, featureModel.getFeatureNames());

		return isWellformed;
	}

	/**
	 * returns true if the constraint causes the feature model to be void
	 * otherwise false
	 * 
	 * @param input
	 *            constraint to be evaluated
	 * @param model
	 *            the feature model
	 * 
	 *            * @throws TimeoutException
	 */
	private boolean voidsModel(final Constraint constraint, String input, FeatureModel model) throws TimeoutException {

		if (!model.getAnalyser().isValid()) {

			return false;
		}
		if (input.length() == 0) {

			return false;
		}
		FeatureModel clonedModel = model.clone();
		NodeReader nodeReader = new NodeReader();

		Node propNode = nodeReader.stringToNode(input, clonedModel.getFeatureNames());
		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removeConstraint(constraint);
			}
			clonedModel.addPropositionalNode(propNode);
			clonedModel.handleModelDataChanged();
		}

		return (!clonedModel.getAnalyser().isValid());

	}
}
