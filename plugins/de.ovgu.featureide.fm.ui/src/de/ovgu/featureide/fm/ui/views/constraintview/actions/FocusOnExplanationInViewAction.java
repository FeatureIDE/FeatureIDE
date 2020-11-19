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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui.views.constraintview.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.FOCUS_ON_EXPLANATION;

import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractConstraintEditorAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.ActionAllowedInExternalSubmodel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FocusOnExplanationOperation;

/**
 * This class represents the action to Focus on the Explanation of a Constraint selected in the Constraint View.
 *
 * @author Rahel Arens
 */
public class FocusOnExplanationInViewAction extends AbstractConstraintEditorAction implements ActionAllowedInExternalSubmodel {

	public static final String ID = "de.ovgu.featureide.focusonexplanationinview";

	IGraphicalFeatureModel graphicalFeatureModel;

	public FocusOnExplanationInViewAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		super(viewer, graphicalFeatureModel.getFeatureModelManager(), FOCUS_ON_EXPLANATION, ID);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/monitor_obj.gif"));
		this.graphicalFeatureModel = graphicalFeatureModel;
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		if ((selection != null) && !selection.isEmpty()) {
			final Object firstElement = selection.getFirstElement();
			if (firstElement instanceof IConstraint) {
				final FeatureModelAnalyzer analyzer = featureModelManager.getVariableFormula().getAnalyzer();
				return analyzer.getExplanation((IConstraint) firstElement) != null;
			}
		}
		return false;
	}

	@Override
	public void run() {
		if ((selection == null) || selection.isEmpty() || !(selection.getFirstElement() instanceof IConstraint)) {
			return;
		}
		final IConstraint constraint = (IConstraint) selection.getFirstElement();
		final FeatureModelAnalyzer analyzer = featureModelManager.getVariableFormula().getAnalyzer();
		final Explanation<?> explanation = analyzer.getExplanation(constraint);

		if (explanation != null) {
			FeatureModelOperationWrapper.run(new FocusOnExplanationOperation(graphicalFeatureModel, (FeatureModelExplanation<?>) explanation));
		}
	}

}
