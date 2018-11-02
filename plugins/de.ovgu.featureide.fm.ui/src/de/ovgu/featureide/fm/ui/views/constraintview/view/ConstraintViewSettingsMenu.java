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
package de.ovgu.featureide.fm.ui.views.constraintview.view;

import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IActionBars;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.MinimalCreateConstraintAction;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.RefreshViewAction;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.ShowCollapsedConstraintAction;

/**
 * This class contains a menu where settings can be set for the ConstraintView
 *
 * @author Domenik Eichhorn
 */

public class ConstraintViewSettingsMenu {
	private ConstraintViewController controller;
	private IGraphicalFeatureModel graphicalModel; // active graphical FeatureModel

	private final ShowCollapsedConstraintAction collapseAction;
	private final RefreshViewAction refreshAction;
	private final MinimalCreateConstraintAction createAction;

	public ConstraintViewSettingsMenu(ConstraintViewController controller) {
		// create actions:
		collapseAction = new ShowCollapsedConstraintAction(null, graphicalModel); // Action that Shows/Hides Collapsed Constraints
		refreshAction = new RefreshViewAction(controller); // Action that lets the user refresh the view manually
		createAction = new MinimalCreateConstraintAction(controller.getCurrentModel()); // Action that lets user create a new constraint
		// create layout:
		update(controller);
		createToolBarLayout();
	}

	/**
	 * updates the current controller, graphicalfeaturemodel and actions (e.g. when the active diagram changed)
	 */
	public void update(ConstraintViewController controller) {
		this.controller = controller;
		if (controller.getView().getViewer().getTree().getHeaderVisible()) {
			if (FeatureModelUtil.getActiveFMEditor() != null) {
				setStatOfActions(true);
				graphicalModel = FeatureModelUtil.getActiveFMEditor().diagramEditor.getGraphicalFeatureModel();
				createAction.update(controller.getCurrentModel());
				refreshAction.update(controller);
				collapseAction.update(graphicalModel);
				if (graphicalModel.getLayout().showCollapsedConstraints()) {
					collapseAction.setImageDescriptor(ImageDescriptor.createFromImage(FMUIPlugin.getImage("collapse.gif")));
					collapseAction.setToolTipText("Hide Collapsed Constraints");
				} else {
					collapseAction.setImageDescriptor(ImageDescriptor.createFromImage(FMUIPlugin.getImage("expand.gif")));
					collapseAction.setToolTipText("Show Collapsed Constraints");
				}
			}
		} else {
			setStatOfActions(false);
		}
	}

	/**
	 * creates the Layout from the toolbar
	 */
	private void createToolBarLayout() {
		final IActionBars actionBars = controller.getViewSite().getActionBars();
		final IToolBarManager toolBarManager = actionBars.getToolBarManager();
		toolBarManager.add(createAction);
		toolBarManager.add(refreshAction);
		toolBarManager.add(collapseAction);
	}

	/**
	 * disables all actions (run method is not called when activated)
	 */
	public void setStatOfActions(Boolean isEnabled) {
		createAction.setEnabled(isEnabled);
		refreshAction.setEnabled(isEnabled);
		collapseAction.setEnabled(isEnabled);
	}

}
