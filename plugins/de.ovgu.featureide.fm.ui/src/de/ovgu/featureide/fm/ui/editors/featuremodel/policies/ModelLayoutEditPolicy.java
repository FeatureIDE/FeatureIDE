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

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.ConstraintDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.FeatureDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.LegendDragAndDropCommand;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;

/**
 * Allows features to be moved onto the feature model diagram.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ModelLayoutEditPolicy extends LayoutEditPolicy {

	private final IGraphicalFeatureModel featureModel;

	private Command cmd;

	public ModelLayoutEditPolicy(IGraphicalFeatureModel featureModel) {
		super();
		this.featureModel = featureModel;
	}

	@Override
	protected EditPolicy createChildEditPolicy(EditPart child) {
		if (child instanceof ConstraintEditPart) {
			return new ConstraintMoveEditPolicy((ConstraintEditPart) child, this);
		} else if (child instanceof FeatureEditPart) {
// TODO _Interface : Removed Code
//			if (featureModel instanceof ExtendedFeatureModel) {
//				IFeature feature = ((FeatureEditPart) child).getFeature();
//				if (feature instanceof ExtendedFeature && ((ExtendedFeature) feature).isFromExtern()) {
//					if (feature.getFeatureModel().getGraphicRepresenation().getLayout().getLayoutAlgorithm() != 0) {
//						return null;
//					}
//				}
//			}
			return new FeatureMoveEditPolicy((FeatureEditPart) child, this);
		} else if (child instanceof LegendEditPart) {
			return new LegendMoveEditPolicy();
		} else {
			return null;
		}
	}

	@Override
	protected Command getMoveChildrenCommand(Request request) {
		cmd = null;
		if (request instanceof ChangeBoundsRequest) {
			final ChangeBoundsRequest r = (ChangeBoundsRequest) request;
			if (r.getEditParts().size() != 1) {
				return null;
			}

			final Object editPart = r.getEditParts().get(0);
			if (editPart instanceof FeatureEditPart) {
				final FeatureEditPart featureEditPart = (FeatureEditPart) editPart;
				final IGraphicalFeature feature = featureEditPart.getModel();
				Rectangle bounds = FeatureUIHelper.getBounds(feature);
				bounds = bounds.getTranslated(r.getMoveDelta().getScaled(1 / FeatureUIHelper.getZoomFactor()));
				cmd = new FeatureDragAndDropCommand(featureModel, feature, bounds.getLocation(), featureEditPart);
			} else if (editPart instanceof ConstraintEditPart) {
				final IGraphicalConstraint constraint = ((ConstraintEditPart) editPart).getModel();

				if (featureModel.getLayout().hasFeaturesAutoLayout()) {
					final Point point = r.getLocation().getCopy();
					getHostFigure().translateToRelative(point);
					cmd = new ConstraintDragAndDropCommand(featureModel, constraint, point);
				} else {
					Rectangle bounds = FeatureUIHelper.getBounds(constraint);
					bounds = bounds.getTranslated(r.getMoveDelta().getScaled(1 / FeatureUIHelper.getZoomFactor()));
					cmd = new ConstraintDragAndDropCommand(featureModel, constraint, bounds.getLocation());
				}
			} else if (editPart instanceof LegendEditPart) {
				cmd = new LegendDragAndDropCommand(featureModel, (LegendEditPart) editPart, r.getMoveDelta());
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
