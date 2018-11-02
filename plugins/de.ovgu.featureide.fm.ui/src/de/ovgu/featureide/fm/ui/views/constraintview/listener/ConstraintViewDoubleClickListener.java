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

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;
import de.ovgu.featureide.fm.ui.views.constraintview.actions.EditConstraintInViewAction;

/**
 * ConstraintView DoubleClickListener
 *
 * @author "Rosiak Kamil"
 */
public class ConstraintViewDoubleClickListener implements IDoubleClickListener {
	private final ConstraintViewController controller;

	public ConstraintViewDoubleClickListener(ConstraintViewController controller) {
		this.controller = controller;
	}

	@Override
	public void doubleClick(DoubleClickEvent event) {
		if (event.getSource() instanceof TreeViewer) {
			final TreeSelection treeSelection = (TreeSelection) event.getSelection();
			if (treeSelection.getFirstElement() instanceof IConstraint) {
				new EditConstraintInViewAction(controller.getView().getViewer(), controller.getCurrentModel()).run();
			}
		}
	}

}
