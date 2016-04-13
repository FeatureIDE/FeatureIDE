/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.policies.ModelLayoutEditPolicy;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * The main editpart that has all <code>FeatureEditPart</code>s as children.
 * Notice that Draw2D calls a figure child of another when its drawn within the
 * parent figure. Therefore, all features need to by direct children of this
 * editpart.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ModelEditPart extends AbstractGraphicalEditPart {

	ModelEditPart(Object featureModel) {
		super();
		setModel(featureModel);
	}

	public IGraphicalFeatureModel getFeatureModel() {
		return (IGraphicalFeatureModel) getModel();
	}

	protected IFigure createFigure() {
		Figure fig = new FreeformLayer();
		fig.setLayoutManager(new FreeformLayout());
		fig.setBorder(new MarginBorder(5));
		return fig;
	}

	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.LAYOUT_ROLE, new ModelLayoutEditPolicy(getFeatureModel()));
	}

	@Override
	protected List<Object> getModelChildren() {
		final IGraphicalFeatureModel fm = getFeatureModel();

		final List<?> constraints = fm.getConstraints();
		final Collection<?> features = Functional.toList(fm.getFeatures());

		final ArrayList<Object> list = new ArrayList<>(constraints.size() + features.size() + 1);

		list.addAll(features);
		list.addAll(constraints);

		if (!FMPropertyManager.isLegendHidden()) {
			list.add(new Legend(fm));
		}

		return list;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gef.editparts.AbstractEditPart#createChild(java.lang.Object)
	 */
	@Override
	public EditPart createChild(Object model) {
		return super.createChild(model);
	}
}
