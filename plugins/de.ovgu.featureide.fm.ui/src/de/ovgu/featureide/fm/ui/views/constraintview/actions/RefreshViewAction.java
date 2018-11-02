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

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * This action refreshed the ConstraintView
 *
 * @author Domenik Eichhorn
 */
public class RefreshViewAction extends Action {
	private static final Image REFRESH_IMG = FMUIPlugin.getImage("refresh_tab.gif");
	private ConstraintViewController controller;

	public RefreshViewAction(ConstraintViewController controller) {
		super("Refresh View", ImageDescriptor.createFromImage(REFRESH_IMG));
		this.controller = controller;
	}

	@Override
	public void run() {
		controller.refreshView(controller.getCurrentModel());
	}

	/**
	 * updates the current controller (needed when switching between feature models)
	 */
	public void update(ConstraintViewController controller) {
		this.controller = controller;
	}

}
