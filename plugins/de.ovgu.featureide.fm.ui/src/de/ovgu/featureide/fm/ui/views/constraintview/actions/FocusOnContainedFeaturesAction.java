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

import static de.ovgu.featureide.fm.core.localization.StringTable.FOCUS_ON_CONTAINED_FEATURES;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ExpandConstraintOperation;

/**
 * This class represents the Action to focus on contained Features of a constraint selected in the ConstraintView.
 *
 * @author Rahel Arens
 */
public class FocusOnContainedFeaturesAction extends Action {

	private IStructuredSelection selection;

	IGraphicalFeatureModel graphicalFeatureModel;

	IConstraint constraint;

	public FocusOnContainedFeaturesAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		super(FOCUS_ON_CONTAINED_FEATURES);
		if (viewer instanceof TreeViewer) {
			selection = (IStructuredSelection) ((TreeViewer) viewer).getSelection();
			setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/monitor_obj.gif"));
			this.graphicalFeatureModel = graphicalFeatureModel;
			setEnabled(isValidSelection(selection));
		}
	}

	@Override
	public void run() {
		final ExpandConstraintOperation op = new ExpandConstraintOperation(graphicalFeatureModel, (IConstraint) selection.getFirstElement());
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	public boolean isValidSelection(IStructuredSelection selection) {
		if ((selection.size() == 1) && (selection.getFirstElement() instanceof IConstraint)) {
			return true;
		}
		return false;
	}
}
