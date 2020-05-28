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
package de.ovgu.featureide.fm.ui.views.constraintview.view;

import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Menu;

import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintAction;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.DeleteConstraintInViewAction;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.EditConstraintInViewAction;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.FocusOnContainedFeaturesInViewAction;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.FocusOnExplanationInViewAction;

/**
 * This class represents the context menu of the ConstraintView.
 *
 * @author Rosiak Kamil
 * @author Rahel Arens
 */
public class ConstraintViewContextMenu {

	ConstraintViewController controller;

	public ConstraintViewContextMenu(ConstraintViewController controller) {
		this.controller = controller;
		createContextMenu(controller.getTreeViewer());
	}

	/**
	 * Creates the context menu
	 */
	protected void createContextMenu(final Viewer viewer) {
		final MenuManager contextMenu = new MenuManager("#ViewerMenu");
		contextMenu.setRemoveAllWhenShown(true);
		contextMenu.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager mgr) {
				if (controller.isConstraintsListVisible()) {
					fillContextMenu(mgr, viewer);
				}
			}
		});

		final Menu menu = contextMenu.createContextMenu(viewer.getControl());
		viewer.getControl().setMenu(menu);
	}

	/**
	 * Fills the dynamic context menu
	 */
	protected void fillContextMenu(IMenuManager contextMenu, Viewer viewer) {
		contextMenu.add(new CreateConstraintAction(viewer, controller.getFeatureModelManager()));
		contextMenu.add(new FocusOnContainedFeaturesInViewAction(viewer, controller.getFeatureModelEditor().diagramEditor.getGraphicalFeatureModel()));
		contextMenu.add(new FocusOnExplanationInViewAction(controller.getFeatureModelEditor().diagramEditor.getGraphicalFeatureModel(), viewer));
		contextMenu.add(new EditConstraintInViewAction(viewer, controller.getFeatureModelManager()));
		contextMenu.add(new DeleteConstraintInViewAction(viewer, controller.getFeatureModelManager()));
	}
}
