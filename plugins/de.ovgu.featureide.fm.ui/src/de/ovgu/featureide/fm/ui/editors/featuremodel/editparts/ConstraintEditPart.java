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
import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.editpolicies.NonResizableEditPolicy;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelReason;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.ConstraintFigure;

/**
 * An editpart to display cross-tree constraints below the feature diagram.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ConstraintEditPart extends ModelElementEditPart {

	public ConstraintEditPart(IGraphicalConstraint constraint) {
		setModel(constraint);
	}

	public IGraphicalConstraint getConstraintModel() {
		return getModel();
	}

	@Override
	public ModelEditPart getParent() {
		return super.getParent();
	}

	@Override
	public IGraphicalConstraint getModel() {
		return (IGraphicalConstraint) super.getModel();
	}

	@Override
	public ConstraintFigure getFigure() {
		return (ConstraintFigure) super.getFigure();
	}

	@Override
	protected ConstraintFigure createFigure() {
		return new ConstraintFigure(getModel());
	}

	@Override
	protected void createEditPolicies() {
		installEditPolicy(EditPolicy.SELECTION_FEEDBACK_ROLE, new NonResizableEditPolicy());
	}

	@Override
	public void performRequest(Request request) {
		final IGraphicalConstraint constraintModel = getModel();
		if (request.getType() == RequestConstants.REQ_OPEN) {
			new ConstraintDialog(constraintModel.getObject().getFeatureModel(), constraintModel.getObject());
		} else if (request.getType() == RequestConstants.REQ_SELECTION) {
			try {
				for (final IFeature containedFeature : constraintModel.getObject().getContainedFeatures()) {
					FeatureUIHelper.getGraphicalFeature(containedFeature, constraintModel.getGraphicalModel()).setConstraintSelected(true);
				}
			} catch (final NullPointerException e) {
				FMCorePlugin.getDefault().reportBug(320);
			}
		}
	}

	@Override
	public void activate() {
		getModel().registerUIObject(this);
		super.activate();
	}

	@Override
	public void deactivate() {
		super.deactivate();
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		final EventType prop = event.getEventType();
		switch (prop) {
		case CONSTRAINT_MOVE:
		case LOCATION_CHANGED:
			getFigure().setLocation(getModel().getLocation());
			break;
		case CONSTRAINT_MODIFY:
		case ATTRIBUTE_CHANGED:
		case CONSTRAINT_SELECTED:
			getFigure().setConstraintProperties();
			getModel().setSize(getFigure().getSize());
			break;
		case ACTIVE_EXPLANATION_CHANGED:
			setActiveReason(null); // reset
			break;
		case ACTIVE_REASON_CHANGED:
			setActiveReason((FeatureModelReason) event.getNewValue());
			break;
		default:
			FMUIPlugin.getDefault().logWarning(event + " @ " + getModel() + " not handled.");
			break;
		}
	}

	/**
	 * <p> Sets the currently active reason. </p>
	 *
	 * <p> Propagates into the figure. Refreshes accordingly. </p>
	 *
	 * @param activeReason the new active reason; null to reset
	 */
	protected void setActiveReason(FeatureModelReason activeReason) {
		getFigure().setActiveReason(activeReason);
		getFigure().setConstraintProperties();
	}
}
