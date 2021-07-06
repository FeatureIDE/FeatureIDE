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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_FEATURE_ABOVE;

import java.util.Iterator;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CreateGraphicalFeatureAboveOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Creates a new feature with the currently selected features as children.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class CreateFeatureAboveAction extends MultipleSelectionAction {

	public static final String ID = "de.ovgu.featureide.createfeatureabove";

	private final IGraphicalFeatureModel graphicalFeatureModel;

	private IFeature parent = null;

	private static ImageDescriptor createImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_OBJ_ADD);

	public CreateFeatureAboveAction(Object viewer, IGraphicalFeatureModel featureModel) {
		super(CREATE_FEATURE_ABOVE, viewer, ID, featureModel.getFeatureModelManager());
		setImageDescriptor(createImage);
		graphicalFeatureModel = featureModel;
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new CreateGraphicalFeatureAboveOperation(graphicalFeatureModel, getSelectedFeatures()));
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (i.e. ModelEditPart is selected)
		if ((selection.size() == 1) && (selection.getFirstElement() instanceof ModelEditPart)) {
			return false;
		}

		// check that selected features have the same parent
		final Iterator<?> iter = selection.iterator();
		parent = null;
		while (iter.hasNext()) {
			final Object editPart = iter.next();
			if (!(editPart instanceof FeatureEditPart) && !(editPart instanceof IFeature)) {
				continue;
			}
			IFeature feature;

			if (editPart instanceof FeatureEditPart) {
				feature = ((FeatureEditPart) editPart).getModel().getObject();
			} else {
				feature = (IFeature) editPart;
			}

			final IFeatureStructure structureParent = feature.getStructure().getParent();
			if (structureParent != null) {
				final IFeature featureParent = structureParent.getFeature();
				if (parent == null) {
					parent = featureParent;
				} else if (parent != featureParent) {
					return false;
				}
			}
		}

		if ((this instanceof ActionAllowedInExternalSubmodel) || !hasExternalFeature(selection)) {
			return true;
		}

		return false;

	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
	}

}
