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

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;

/**
 * A modified CreateConstraintAction for the ConstraintView
 *
 * @author Domenik Eichhorn
 */
public class CreateConstraintInViewAction extends Action {

	public static final String ID = "de.ovgu.featureide.createconstraintinview";
	private final ConstraintViewController controller;

	private static ImageDescriptor createImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD);

	public CreateConstraintInViewAction(ConstraintViewController controller) {
		super(StringTable.CREATE_CONSTRAINT, createImage);
		this.controller = controller;
	}

	@Override
	public void run() {
		new ConstraintDialog(controller.getFeatureModelManager(), null);
	}
}
