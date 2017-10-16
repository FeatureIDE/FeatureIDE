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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartFactory;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;

/**
 * Creates editparts for given models.
 *
 * @author Constanze Adler
 */
public class GraphicalEditPartFactory implements EditPartFactory {

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.gef.EditPartFactory#createEditPart(org.eclipse.gef.EditPart, java.lang.Object)
	 */
	@Override
	public EditPart createEditPart(EditPart editPart, Object model) {
		if (model instanceof FSTModel) {
			return new ModelEditPart((FSTModel) model);
		}
		if (model instanceof FSTRole) {
			return new RoleEditPart((FSTRole) model);
		}
		if (model instanceof FSTClass) {
			return new ClassEditPart((FSTClass) model);
		}
		if (model instanceof FSTFeature) {
			return new CollaborationEditPart((FSTFeature) model);
		}
		return null;
	}

}
