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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FocusOnExplanationOperation;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;

/**
 * This class represents the action to Focus on the Explanation of a Constraint selected in the Constraint View.
 *
 * @author Rahel Arens
 */
public class FocusOnExplanationInViewAction extends Action {

	IGraphicalFeatureModel graphicalFeatureModel;

	FeatureModelAnalyzer analyzer = null;

	IStructuredSelection selection;

	IFeature iFeature = null;

	IConstraint constraint;

	public FocusOnExplanationInViewAction(IGraphicalFeatureModel graphicalFeatureModel, Object viewer) {
		super(FOCUS_ON_EXPLANATION);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/monitor_obj.gif"));
		this.graphicalFeatureModel = graphicalFeatureModel;
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			constraint = (IConstraint) selection.getFirstElement();
			setEnabled(hasExplanation(selection));
		}
	}

	@Override
	public void run() {
		if (constraint.getFeatureModel().getAnalyser().getExplanation(constraint) != null) {
			final FeatureModelExplanation explanation = (FeatureModelExplanation) constraint.getFeatureModel().getAnalyser().getExplanation(constraint);
			final FocusOnExplanationOperation op = new FocusOnExplanationOperation(graphicalFeatureModel, explanation);
			try {
				PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
			} catch (final ExecutionException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		} else {
			for (final IFeature feature : FeatureModelUtil.getFeatureModel().getFeatures()) {
				if (feature.getFeatureModel().getAnalyser().getExplanation(feature) != null) {
					for (final Object reason : feature.getFeatureModel().getAnalyser().getExplanation(feature).getReasons()) {
						if (reason instanceof FeatureModelReason) {
							final FeatureModelReason fmReason = (FeatureModelReason) reason;
							if (fmReason.getSubject().getElement() instanceof IConstraint) {
								if (fmReason.getSubject().getElement().equals(constraint)) {
									final FeatureModelExplanation fme =
										(FeatureModelExplanation) feature.getFeatureModel().getAnalyser().getExplanation(feature);
									final FocusOnExplanationOperation op = new FocusOnExplanationOperation(graphicalFeatureModel, fme);
									try {
										PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
									} catch (final ExecutionException e) {
										FMUIPlugin.getDefault().logError(e);
									}
								}
							}
						}
					}
				}
			}
		}

	}

	public boolean hasExplanation(IStructuredSelection sel) {
		if ((constraint.getConstraintAttribute() == ConstraintAttribute.REDUNDANT) || (constraint.getConstraintAttribute() == ConstraintAttribute.UNSATISFIABLE)
			|| (constraint.getConstraintAttribute() == ConstraintAttribute.VOID_MODEL) || (constraint.getConstraintAttribute() == ConstraintAttribute.DEAD)
			|| ((constraint.getConstraintAttribute() == ConstraintAttribute.IMPLICIT)
				|| (constraint.getConstraintAttribute() == ConstraintAttribute.TAUTOLOGY))) {
			return true;
		}
		return false;
	}
}
