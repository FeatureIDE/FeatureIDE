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
package de.ovgu.featureide.fm.ui.editors.featuremodel.policies;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.requests.ChangeBoundsRequest;
import org.eclipse.gef.requests.CreateRequest;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.ConstraintDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.FeatureDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.LegendDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * Allows features to be moved onto the feature model diagram.
 * 
 * @author Thomas Thuem
 */
public class ModelLayoutEditPolicy extends LayoutEditPolicy {

	private final FeatureModel featureModel;

	private Command cmd;

	public ModelLayoutEditPolicy(FeatureModel featureModel) {
		super();
		this.featureModel = featureModel;
	}

	@Override
	protected EditPolicy createChildEditPolicy(EditPart child) {
		if (child instanceof ConstraintEditPart)
			return new ConstraintMoveEditPolicy((ConstraintEditPart) child,
					this);
		if (child instanceof FeatureEditPart)
			return new FeatureMoveEditPolicy((FeatureEditPart) child, this);
		if (child instanceof LegendEditPart)
			return new LegendMoveEditPolicy((LegendEditPart) child, this);
		return null;
	}

	@Override
	protected Command getMoveChildrenCommand(Request request) {
		cmd = null;
		if (request instanceof ChangeBoundsRequest) {
			ChangeBoundsRequest r = (ChangeBoundsRequest) request;
			if (r.getEditParts().size() != 1)
				return null;
			if (r.getEditParts().get(0) instanceof FeatureEditPart) {
				FeatureEditPart editPart = (FeatureEditPart) r.getEditParts()
						.get(0);
				Feature feature = editPart.getFeature();
				Rectangle bounds = FeatureUIHelper.getBounds(feature);
				bounds = r.getTransformedRectangle(bounds);
				cmd = new FeatureDragAndDropCommand(featureModel, feature,
						bounds.getLocation(),editPart);
			}
			if (r.getEditParts().get(0) instanceof ConstraintEditPart) {
				ConstraintEditPart editPart = (ConstraintEditPart) r
						.getEditParts().get(0);
				Constraint constraint = editPart.getConstraintModel();

				if (featureModel.getLayout().hasFeaturesAutoLayout()){
					Point point = r.getLocation().getCopy();
					getHostFigure().translateToRelative(point);

					cmd = new ConstraintDragAndDropCommand(featureModel,
							constraint, point);
				} else {
					Rectangle bounds = FeatureUIHelper.getBounds(constraint);
					bounds = r.getTransformedRectangle(bounds);
					cmd = new ConstraintDragAndDropCommand(featureModel,
							constraint, bounds.getLocation());
				}

			}
			if (r.getEditParts().get(0) instanceof LegendEditPart) {
				LegendEditPart editPart = (LegendEditPart) r.getEditParts()
						.get(0);

				cmd = new LegendDragAndDropCommand(featureModel,
						(LegendFigure) editPart.getFigure());

			}
		}
		return cmd;
	}

	public Command getConstraintCommand() {
		return cmd;
	}
	
	@Override
	protected Command getCreateCommand(CreateRequest request) {
		// no creation supported
		
		return null;
	}

}
