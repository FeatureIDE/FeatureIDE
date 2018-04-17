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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONSTRAINT;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Creates a new propositional constraint below the feature diagram.
 *
 * @author Christian Becker
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class CreateConstraintAction extends AbstractConstraintEditorAction {

	public static final String ID = "de.ovgu.featureide.createconstraint";

	private static ImageDescriptor createImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD);

	public CreateConstraintAction(Object viewer, IFeatureModel featuremodel) {
		super(viewer, featuremodel, CREATE_CONSTRAINT, ID);
		setImageDescriptor(createImage);
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		return true;
	}

	@Override
	public void run() {
		super.run();
		openEditor(null);
	}

}
