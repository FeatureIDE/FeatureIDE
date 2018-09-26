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
package de.ovgu.featureide.fm.ui.views.constraintview.listener;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWorkbenchPartReference;

import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.utils.FeatureModelUtil;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * TODO description
 *
 * @author "Rosiak Kamil"
 */
public class ConstraintViewPartListener implements IPartListener2 {
	ConstraintViewController controller;

	/**
	 *
	 */
	public ConstraintViewPartListener(ConstraintViewController cvc) {
		controller = cvc;
	}

	@Override
	public void partOpened(IWorkbenchPartReference part) {
		if (part.getId().equals(ConstraintViewController.ID)) {
			controller.setConstraintsHidden(true);
		}
	}

	@Override
	public void partDeactivated(IWorkbenchPartReference part) {}

	@Override
	public void partClosed(IWorkbenchPartReference part) {
		if (part instanceof FeatureModelEditor) {
			if ((FeatureModelUtil.getActiveFMEditor() == part) || (FeatureModelUtil.getActiveFMEditor() == null)) {
				final FeatureModelEditor editor = (FeatureModelEditor) part.getPart(false);
				controller.addPageChangeListener(editor);
				controller.getTreeViewer().refresh();
			}
		}
	}

	@Override
	public void partBroughtToTop(IWorkbenchPartReference part) {
		if (part.getPart(false) instanceof FeatureModelEditor) {
			controller.checkForRefresh();
		} else {
			controller.getView().addNoFeatureModelItem();
		}
	}

	@Override
	public void partActivated(IWorkbenchPartReference part) {
		if (part.getPart(false) instanceof FeatureModelEditor) {
			controller.checkForRefresh();
		} else if ((part.getPart(false) instanceof ConstraintViewController) && (FeatureModelUtil.getActiveFMEditor() != null)) {
			controller.checkForRefresh();
		}
		if (part.getPart(false) instanceof IEditorPart) {
			controller.setConstraintsHidden(controller.isConstraintsHidden());
		}
	}

	@Override
	public void partHidden(IWorkbenchPartReference part) {
		if (part.getId().equals(ConstraintViewController.ID)) {
			controller.setConstraintsHidden(false);
		}
	}

	@Override
	public void partVisible(IWorkbenchPartReference part) {
		if (part.getId().equals(ConstraintViewController.ID)) {
			controller.setConstraintsHidden(true);
		}
	}

	@Override
	public void partInputChanged(IWorkbenchPartReference partRef) {}

}
