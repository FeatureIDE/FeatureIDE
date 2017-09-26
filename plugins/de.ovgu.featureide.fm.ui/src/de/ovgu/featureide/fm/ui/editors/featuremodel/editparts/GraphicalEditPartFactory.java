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
package de.ovgu.featureide.fm.ui.editors.featuremodel.editparts;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartFactory;

import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;

/**
 * Creates edit parts for given models.
 *
 * @author Thomas Thuem
 */
public class GraphicalEditPartFactory implements EditPartFactory {

	@Override
	public EditPart createEditPart(EditPart context, Object model) {
		if (model instanceof IGraphicalFeature) {
			return new FeatureEditPart((IGraphicalFeature) model);
		} else if (model instanceof IGraphicalFeatureModel) {
			return new ModelEditPart((IGraphicalFeatureModel) model);
		} else if (model instanceof FeatureConnection) {
			return new ConnectionEditPart((FeatureConnection) model);
		} else if (model instanceof IGraphicalConstraint) {
			return new ConstraintEditPart((IGraphicalConstraint) model);
		} else if (model instanceof Legend) {
			return new LegendEditPart((Legend) model);
		} else {
			throw new UnsupportedOperationException("Not implememented for " + model.getClass());
		}

	}

}
