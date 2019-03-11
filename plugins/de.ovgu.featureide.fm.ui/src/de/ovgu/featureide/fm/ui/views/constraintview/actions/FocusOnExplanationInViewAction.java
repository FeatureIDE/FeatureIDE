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
package de.ovgu.featureide.fm.ui.views.constraintview.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.FOCUS_ON_EXPLANATION;

import java.util.concurrent.locks.Lock;

import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractConstraintEditorAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FocusOnExplanationOperation;

/**
 * This class represents the action to Focus on the Explanation of a Constraint selected in the Constraint View.
 *
 * @author Rahel Arens
 */
public class FocusOnExplanationInViewAction extends AbstractConstraintEditorAction {
	public static final String ID = "de.ovgu.featureide.focusonexplanationinview";

	private final IGraphicalFeatureModel graphicalFeatureModel;
	private IConstraint constraint;

	public FocusOnExplanationInViewAction(IGraphicalFeatureModel graphicalFeatureModel, Object viewer) {
		super(viewer, graphicalFeatureModel.getFeatureModelManager(), FOCUS_ON_EXPLANATION, ID);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/monitor_obj.gif"));
		this.graphicalFeatureModel = graphicalFeatureModel;
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		if ((selection != null) && !selection.isEmpty()) {
			final Object firstElement = selection.getFirstElement();
			if (firstElement instanceof IConstraint) {
				constraint = (IConstraint) firstElement;
				return hasExplanation(constraint);
			}
		}
		constraint = null;
		return false;
	}

	@Override
	public void run() {
		final IFeatureModelManager fmManager = graphicalFeatureModel.getFeatureModelManager();
		final Lock fileOperationLock = fmManager.getFileOperationLock();
		fileOperationLock.lock();
		try {
			final IFeatureModel featureModel = fmManager.editObject();
			final FeatureModelAnalyzer analyser = featureModel.getAnalyser();
			if (constraint == null) {
				if (!analyser.valid()) {
					FeatureModelOperationWrapper.run(new FocusOnExplanationOperation(graphicalFeatureModel, analyser.getVoidFeatureModelExplanation()));
				}
			} else if (featureModel == constraint.getFeatureModel()) {
				if (analyser.getExplanation(constraint) != null) {
					FeatureModelOperationWrapper.run(new FocusOnExplanationOperation(graphicalFeatureModel,
							(FeatureModelExplanation<?>) constraint.getFeatureModel().getAnalyser().getExplanation(constraint)));
					// Check if any feature has this constraint as a reason in its explanation
				} else {
					for (final IFeature feature : featureModel.getFeatures()) {
						// Check if Feature has an Explanation
						final Explanation<?> featureExplanation = analyser.getExplanation(feature);
						if ((featureExplanation != null) && constraintIsInExplanation(featureExplanation)) {
							FeatureModelOperationWrapper.run(new FocusOnExplanationOperation(graphicalFeatureModel,
									(FeatureModelExplanation<?>) feature.getFeatureModel().getAnalyser().getExplanation(feature)));
						}
					}
				}
			}
		} finally {
			fileOperationLock.unlock();
		}
	}

	/**
	 * This method checks if the constraint appears in a given Explanation
	 */
	private boolean constraintIsInExplanation(Explanation<?> featureExplanation) {
		// Iterate Reasons
		for (final Object reason : featureExplanation.getReasons()) {
			if (reason instanceof FeatureModelReason) {
				final FeatureModelReason fmReason = (FeatureModelReason) reason;
				// Check if this Constraint is one of the reasons
				if (fmReason.getSubject().getElement().equals(constraint)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * This method checks if the selection has some explanation.
	 *
	 * @return If selection has explanation true else false.
	 */
	public boolean hasExplanation(IConstraint constraint) {
		return (constraint != null) && ((constraint.getConstraintAttribute() == ConstraintAttribute.REDUNDANT)
			|| (constraint.getConstraintAttribute() == ConstraintAttribute.UNSATISFIABLE)
			|| (constraint.getConstraintAttribute() == ConstraintAttribute.VOID_MODEL) || (constraint.getConstraintAttribute() == ConstraintAttribute.DEAD)
			|| (constraint.getConstraintAttribute() == ConstraintAttribute.IMPLICIT) || (constraint.getConstraintAttribute() == ConstraintAttribute.TAUTOLOGY)
			|| (!constraint.getFeatureModel().getAnalyser().valid()));
	}

}
