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
package de.ovgu.featureide.fm.ui.views.constraintview.listener;

import org.eclipse.jface.action.Action;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;

import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.DeleteConstraintInViewAction;
import de.ovgu.featureide.fm.ui.views.constraintview.view.ConstraintView;

/**
 * ConstraintView KeyListener
 *
 * @author Rosiak Kamil
 */
public class ConstraintViewKeyListener implements KeyListener {

	// integer values that are returned when pressing a special button (from keyListener)
	private final int F_BUTTON_PRESSED = 102;

	private final ConstraintViewController controller;
	private final ConstraintView viewer;

	public ConstraintViewKeyListener(ConstraintViewController controller) {
		this.controller = controller;
		viewer = controller.getView();
	}

	@Override
	public void keyPressed(KeyEvent e) {
		if (e.keyCode == SWT.DEL) {
			// pressing the del button while having a constraint selected will delete it
			final Action deleteAction = new DeleteConstraintInViewAction(viewer.getViewer(), controller.getFeatureModelManager());
			if (deleteAction.isEnabled()) {
				deleteAction.run();
			}
		} else if (((e.stateMask == (SWT.CTRL)) && (e.keyCode == F_BUTTON_PRESSED))) {
			// pressing CTRL + F will get you in the search box
			viewer.getSearchBox().setFocus();
		} else if (e.keyCode == SWT.ESC) {
			// pressing the escape button will remove the focus or current selection
			viewer.getViewer().setSelection(null);
		}
	}

	@Override
	public void keyReleased(KeyEvent e) {}

}
