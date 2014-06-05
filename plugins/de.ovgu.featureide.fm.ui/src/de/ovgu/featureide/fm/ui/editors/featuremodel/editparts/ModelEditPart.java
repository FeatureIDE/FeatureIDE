/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.editparts;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayer;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
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
 */
public class ModelEditPart extends AbstractGraphicalEditPart {
	
	public ModelEditPart(FeatureModel featureModel) {
		super();
		setModel(featureModel);
	}
	
	public FeatureModel getFeatureModel() {
		return (FeatureModel) getModel();
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
		LinkedList<Object> list = new LinkedList<Object>();
		addFeatures(getFeatureModel().getRoot(), list);
		if(!FMPropertyManager.isLegendHidden()) {
			list.add(new Legend((FeatureModel)getModel()));
		}
		addConstraints(getFeatureModel().getConstraints(), list);
		return list;
	}

	private void addFeatures(Feature feature, List<Object> list) {
		if (feature == null)
			return;
		list.add(feature);
		for (Feature child : feature.getChildren())
			addFeatures(child, list);
	}
	
	private void addConstraints(List<Constraint> constraints, List<Object> list) {
		list.addAll(constraints);
	}

}
