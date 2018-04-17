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

import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.policies.LegendMoveEditPolicy;

/**
 * EditPart for feature model legend
 *
 * @author Fabian Benduhn
 */
public class LegendEditPart extends AbstractGraphicalEditPart {

	LegendEditPart(Legend legend) {
		setModel(legend);
	}

	@Override
	public ModelEditPart getParent() {
		return (ModelEditPart) super.getParent();
	}

	@Override
	public Legend getModel() {
		return (Legend) super.getModel();
	}

	@Override
	public LegendFigure getFigure() {
		return (LegendFigure) super.getFigure();
	}

	@Override
	protected LegendFigure createFigure() {
		return new LegendFigure(getModel().getModel(), getModel().getPos());
	}

	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.PRIMARY_DRAG_ROLE, new LegendMoveEditPolicy());
	}

}
