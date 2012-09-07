/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.editparts;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.ConstraintFigure;

/**
 * An editpart to display cross-tree constraints below the feature diagram.
 * 
 * @author Thomas Thuem
 */
public class ConstraintEditPart extends AbstractGraphicalEditPart implements
		PropertyConstants, PropertyChangeListener {

	public ConstraintEditPart(Constraint constraint) {
		super();
		setModel(constraint);
	}

	public Constraint getConstraintModel() {
		return (Constraint) getModel();
	}

	public ConstraintFigure getConstraintFigure() {
		return (ConstraintFigure) getFigure();
	}

	@Override
	protected IFigure createFigure() {
		return new ConstraintFigure(getConstraintModel());
	}

	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.SELECTION_FEEDBACK_ROLE, new NonResizableEditPolicy());

	}

	public void performRequest(Request request) {
		
		for(Feature feature : getConstraintModel().getFeatureModel().getFeatures())	{
			if (feature.isConstraintSelected()) feature.setConstraintSelected(false);
		}
		
		if (request.getType() == RequestConstants.REQ_OPEN) {
			new ConstraintDialog(getConstraintModel().getFeatureModel(),
					getConstraintModel());					
		} else if (request.getType() == RequestConstants.REQ_SELECTION) {
			try {
				for (Feature containedFeature : getConstraintModel().getContainedFeatures()){
					containedFeature.setConstraintSelected(true);
				}
			} catch (NullPointerException e){
				FMCorePlugin.getDefault().reportBug(320);
			}
		}
	}

	@Override
	public void activate() {
		getConstraintModel().addListener(this);
		super.activate();
	}

	@Override
	public void deactivate() {
		super.deactivate();
		getConstraintModel().removeListener(this);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.beans.PropertyChangeListener#propertyChange(java.beans.
	 * PropertyChangeEvent)
	 */
	public void propertyChange(PropertyChangeEvent event) {
		String prop = event.getPropertyName();
		if (prop.equals(LOCATION_CHANGED)) {
			getConstraintFigure().setLocation((Point) event.getNewValue());
		} else if (prop.equals(ATTRIBUTE_CHANGED)) {
			getConstraintFigure().setConstraintProperties(false);
		} else if (prop.equals(CONSTRAINT_SELECTED)) {
			getConstraintFigure().setConstraintProperties(false);
		}
	}

}
