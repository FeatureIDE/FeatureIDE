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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONSTRAINT;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.impl.MultiConstraint;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;

/**
 * Creates a new propositional constraint below the feature diagram.
 *
 * @author Christian Becker
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class CreateConstraintAction extends AbstractConstraintEditorAction implements ActionAllowedInExternalSubmodel {

	public static final String ID = "de.ovgu.featureide.createconstraint";

	private static ImageDescriptor createImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD);

	public CreateConstraintAction(Object viewer, IFeatureModelManager featureModelManager) {
		this(viewer, featureModelManager, ID);
	}

	protected CreateConstraintAction(Object viewer, IFeatureModelManager featureModelManager, String id) {
		super(viewer, featureModelManager, CREATE_CONSTRAINT, id);
		setImageDescriptor(createImage);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		if (selection.toList().stream().filter(o -> o instanceof ConstraintEditPart)
				.filter(o -> ((ConstraintEditPart) o).getModel().getObject() instanceof MultiConstraint)
				.anyMatch(c -> ((MultiConstraint) ((ConstraintEditPart) c).getModel().getObject()).isFromExtern())) {
			return false;
		}
		return true;
	}

	@Override
	public void run() {
		openEditor(null);
	}

}
