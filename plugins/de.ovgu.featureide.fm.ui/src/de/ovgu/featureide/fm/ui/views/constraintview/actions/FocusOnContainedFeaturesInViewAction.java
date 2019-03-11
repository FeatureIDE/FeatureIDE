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

import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ExpandConstraintOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * This class represents the Action to focus on contained Features of a constraint selected in the ConstraintView.
 *
 * @author Rahel Arens
 */
public class FocusOnContainedFeaturesInViewAction extends Action {
	private IStructuredSelection selection;
	private IGraphicalFeatureModel graphicalFeatureModel;

	public FocusOnContainedFeaturesInViewAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
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
		FeatureModelOperationWrapper.run(new ExpandConstraintOperation(graphicalFeatureModel, (IConstraint) selection.getFirstElement()));
	}

	/**
	 * this method verifies the selection.
	 *
	 * @return returns true if this action can process the selected items else false.
	 */
	public boolean isValidSelection(IStructuredSelection selection) {
		if ((selection.size() == 1) && (selection.getFirstElement() instanceof IConstraint)) {
			return true;
		}
		return false;
	}
}
