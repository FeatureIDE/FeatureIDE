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

import static de.ovgu.featureide.fm.core.localization.StringTable.RUNNING_ADDITIONAL_CHECKS___;

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
import org.prop4j.Implies;
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Class which contains several tests for {@link ConstraintDialog} text field, which contains user written constraints.
 *
 * @author Marcus Pinnecke
 */
public final class ConstraintTextValidator {

	/**
	 * returns a List of all features that are caused to be dead by the constraint input
	 *
	 * @param input constraint to be evaluated
	 * @param model the feature model
	 * @return List of all dead Features, empty if no feature is caused to be dead
	 */
	private SortedSet<IFeature> getDeadFeatures(IConstraint constraint, String input, IFeatureModel model) {
		Collection<IFeature> deadFeaturesBefore = null;
		final IFeatureModel clonedModel = model.clone(null);

		final NodeReader nodeReader = new NodeReader();

		final Node propNode = nodeReader.stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(clonedModel.getFeatures())));

		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removeConstraint(constraint);
			}
			deadFeaturesBefore = clonedModel.getAnalyser().getDeadFeatures();
			clonedModel.addConstraint(new Constraint(clonedModel, propNode));
			clonedModel.handleModelDataChanged();
		}

		final SortedSet<IFeature> deadFeaturesAfter = new TreeSet<IFeature>(new FeatureComparator(true));

		for (final IFeature l : clonedModel.getAnalyser().getDeadFeatures()) {
			if (!deadFeaturesBefore.contains(l)) {
				deadFeaturesAfter.add(l);

			}
		}
		return deadFeaturesAfter;
	}

	/**
	 * returns a String to be displayed in the dialog header contains the list of dead features
	 *
	 * @param deadFeatures List of dead Features
	 **/
	private String getDeadFeatureString(Set<IFeature> deadFeatures) {
		final StringBuilder featureString = new StringBuilder();
		featureString.append("Constraint causes the following features to be dead: ");
		int count = 0;
		int featureCount = 0;
		boolean isNewLine = false;
		for (final IFeature l : deadFeatures) {
			count = count + l.toString().length() + 2;

			if ((isNewLine == false) && (count > 35)) {
				featureString.append('\n');
				isNewLine = true;
			}
			if (count < 90) {
				featureString.append(l.getName());
				if (featureCount < (deadFeatures.size() - 1)) {
					featureString.append(", ");
				}
				featureCount++;

			}

		}
		if (featureCount < deadFeatures.size()) {
			featureString.append("...");
		}
		return featureString.toString();
	}

	private List<IFeature> getFalseOptional(IConstraint constraint, String input, IFeatureModel model) {
		final List<IFeature> list = new ArrayList<IFeature>();
		final IFeatureModel clonedModel = model.clone(null);

		final NodeReader nodeReader = new NodeReader();

		final Node propNode = nodeReader.stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(clonedModel.getFeatures())));

		// The following code fixes issue #406; should be enhanced in further development
		// to not always clone the whole feature model for every performed analysis
		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removeConstraint(constraint);
			}
		}

		for (final IFeature feature : model.getFeatures()) {
			if (input.contains(feature.getName())) {
				// if (feature.getFeatureStatus() != FeatureStatus.FALSE_OPTIONAL) {
				clonedModel.addConstraint(new Constraint(clonedModel, propNode));
				clonedModel.getAnalyser().analyzeFeatureModel(null);
				if ((clonedModel.getFeature(feature.getName()).getProperty().getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL) && !list.contains(feature)) {
					list.add(feature);
					// }
				}
			}
		}

		return list;
	}

	private String getFalseOptionalString(List<IFeature> list) {
		final String listString = Functional.join(list, ",", FeatureUtils.GET_FEATURE_NAME);
		final String featureString = "Constraint causes the following features to be false optional: " + '\n';
		return featureString + listString;
	}

	/**
	 * Tests if the {@link IConstraint} will change the product line.
	 *
	 * @param constraint The actual {@link IConstraint}
	 * @return <code>true</code> if the {@link IConstraint} is redundant
	 */
	private boolean isRedundant(IConstraint constraint, final IFeatureModel featureModel, String input, final int timeOut) {
		if (input.length() == 0) {
			return false;
		}
		final IFeatureModel clonedModel = featureModel.clone(null);
		final Node propNode = new NodeReader().stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(clonedModel.getFeatures())));

		// The following code fixes issue #406; should be enhanced in further development
		// to not always clone the whole feature model for every performed analysis
		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removeConstraint(constraint);
			}
		}

		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(clonedModel);
		final Node check = new Implies(nodeCreator.createNodes(), propNode);

		final SatSolver satsolver = new SatSolver(new Not(check), timeOut);

		try {
			return !satsolver.isSatisfiable();
		} catch (final TimeoutException e) {
			return true;
		}
	}

	/**
	 * returns true if constraint is satisfiable otherwise false
	 *
	 * @param constraint the constraint to be evaluated
	 * @param timeout timeout in ms
	 */
	public static boolean isSatisfiable(String constraint, int timeout) {
		final NodeReader nodeReader = new NodeReader();
		final SatSolver satsolver = new SatSolver(nodeReader.stringToNode(constraint).clone(), timeout);
		try {
			return satsolver.isSatisfiable();
		} catch (final TimeoutException e) {
			FMUIPlugin.getDefault().logError(e);
			return true;
		}

	}

	/**
	 * returns true if the constraint is always true
	 *
	 * @param constraint the constraint to be evaluated
	 * @param timeout timeout in ms
	 *
	 */
	private boolean isTautology(String constraint, int timeout) {
		final NodeReader nodeReader = new NodeReader();
		final Node node = nodeReader.stringToNode(constraint);

		final SatSolver satsolver = new SatSolver(new Not(node.clone()), timeout);

		try {
			return !satsolver.isSatisfiable();
		} catch (final TimeoutException e) {

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
			validationResult = result;
			details = message;
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
			canceled = true;
		}
	}

	/**
	 * Runs tests not blocking the current GUI thread. The result will be returned each test's result and a separate notification before the first tests starts
	 * and (in case of all test has passed) when the entire series has ended.
	 *
	 * @param constraint Constraint
	 * @param timeOut Timeout
	 * @param featureModel FeatureModel
	 * @param constraintText Test to text
	 * @param onCheckStarted Observer, before the first test runs.
	 * @param onVoidsModelCheckComplete Observer, when there is a result for VOIDS_MODEL test
	 * @param onFalseOptionalCheckComplete Observer, when there is a result for FALSE_OPTIONAL test
	 * @param onDeadFeatureCheckComplete Observer, when there is a result for DEAD_FEATURE test
	 * @param onIsRedundantCheckComplete Observer, when there is a result for REDUNDANT_CHECK test
	 * @param onIsTautology Observer, when there is a result for "tautology" test
	 * @param onIsNotSatisfiable Observer, when there is a result for IS_SATISFIABLE test
	 * @param onCheckEnded Observer, when the entire series has passed and ended
	 */
	public void validateAsync(final IConstraint constraint, final int timeOut, final IFeatureModel featureModel, final String constraintText,
			final IConsumer<ValidationMessage> onCheckStarted, final IConsumer<ValidationMessage> onVoidsModelCheckComplete,
			final IConsumer<ValidationMessage> onFalseOptionalCheckComplete, final IConsumer<ValidationMessage> onDeadFeatureCheckComplete,
			final IConsumer<ValidationMessage> onIsRedundantCheckComplete, final IConsumer<ValidationMessage> onCheckEnded,
			final IConsumer<ValidationMessage> onIsTautology, final IConsumer<ValidationMessage> onIsNotSatisfiable) {

		final String con = constraintText.trim();

		cancelValidation();

		asyncCheckJob = new ValidationJob(RUNNING_ADDITIONAL_CHECKS___) {

			@Override
			protected IStatus run(IProgressMonitor monitor) {

				updateUI(onCheckStarted, "");
				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundTautology = isTautology(con, timeOut);

					if (problemFoundTautology) {
						updateUI(onIsTautology, "");
						return Status.OK_STATUS;
					}
				}

				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundNotSatisfiable = !isSatisfiable(con, timeOut);

					if (problemFoundNotSatisfiable) {
						updateUI(onIsNotSatisfiable, "");
						return Status.OK_STATUS;
					}
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundVoidsModel = isVoidsModel(featureModel, con, constraint);

					if (problemFoundVoidsModel) {
						updateUI(onVoidsModelCheckComplete, "");
						return Status.OK_STATUS;
					}
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final List<IFeature> falseOptionalFeatures = getFalseOptional(constraint, con, featureModel);

					if (!falseOptionalFeatures.isEmpty()) {
						updateUI(onFalseOptionalCheckComplete, getFalseOptionalString(falseOptionalFeatures));
						return Status.OK_STATUS;
					}
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final Set<IFeature> deadFeatuers = getDeadFeatures(constraint, con, featureModel);

					if (!deadFeatuers.isEmpty()) {
						updateUI(onDeadFeatureCheckComplete, getDeadFeatureString(deadFeatuers));
						return Status.OK_STATUS;
					}
				}
				// ---------------------------------------------------------
				if (!canceled) {
					final boolean problemFoundRedundant = isRedundant(constraint, featureModel, con, timeOut);

					if (problemFoundRedundant) {
						updateUI(onIsRedundantCheckComplete, "");
						return Status.OK_STATUS;
					}
				}
				// ---------------------------------------------------------
				if (!canceled) {
					updateUI(onCheckEnded, "");
				}

				return Status.OK_STATUS;
			}

			private void updateUI(final IConsumer<ValidationMessage> consumer, final String message) {
				if (!canceled) {
					new UIJob("Updating ConstraintDialog Message") {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {
							if (!canceled) {
								consumer.invoke(new ValidationMessage(null, message));
							}
							return Status.OK_STATUS;
						}
					}.schedule();
				}
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
	private boolean isVoidsModel(IFeatureModel featureModel, String con, IConstraint constraint) {
		try {
			return voidsModel(constraint, con, featureModel);
		} catch (final TimeoutException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * returns true if the constraint causes the feature model to be void otherwise false
	 *
	 * @param input constraint to be evaluated
	 * @param model the feature model
	 *
	 *        * @throws TimeoutException
	 */
	private boolean voidsModel(final IConstraint constraint, String input, IFeatureModel model) throws TimeoutException {
		if (!model.getAnalyser().isValid()) {

			return false;
		}
		if (input.length() == 0) {

			return false;
		}
		final IFeatureModel clonedModel = model.clone(null);
		final NodeReader nodeReader = new NodeReader();

		final Node propNode = nodeReader.stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(clonedModel.getFeatures())));
		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removeConstraint(constraint);
			}
			clonedModel.addConstraint(new Constraint(clonedModel, propNode));
			clonedModel.handleModelDataChanged();
		}

		return (!clonedModel.getAnalyser().isValid());

	}
}
