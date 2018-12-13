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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.draw2d.IFigure;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.RootEditPart;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.ModelFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.policies.ModelLayoutEditPolicy;

/**
 * The main editpart that has all <code>FeatureEditPart</code>s as children. Notice that Draw2D calls a figure child of another when its drawn within the parent
 * figure. Therefore, all features need to by direct children of this editpart.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ModelEditPart extends AbstractGraphicalEditPart {

	ModelEditPart(IGraphicalFeatureModel featureModel) {
		setModel(featureModel);
	}

	public IGraphicalFeatureModel getFeatureModel() {
		return getModel();
	}

	@Override
	public RootEditPart getParent() {
		final EditPart parent = super.getParent();
		return (RootEditPart) parent;
	}

	@Override
	public IGraphicalFeatureModel getModel() {
		final Object model = super.getModel();
		return (IGraphicalFeatureModel) model;
	}

	@Override
	public ModelFigure getFigure() {
		final IFigure figure2 = super.getFigure();
		return (ModelFigure) figure2;
	}

	@Override
	protected ModelFigure createFigure() {
		return new ModelFigure();
	}

	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.LAYOUT_ROLE, new ModelLayoutEditPolicy(getModel()));
	}

	@Override
	protected List<Object> getModelChildren() {
		final IGraphicalFeatureModel fm = getModel();

		final List<IGraphicalConstraint> constraints = fm.getVisibleConstraints();
		final Collection<IGraphicalFeature> features = fm.getVisibleFeatures();

		final ArrayList<Object> list = new ArrayList<>(constraints.size() + features.size() + 1);

		list.addAll(features);
		list.addAll(constraints);

		if (!fm.isLegendHidden()) {
			list.add(fm.getLegend());
		}

		return list;
	}
}
