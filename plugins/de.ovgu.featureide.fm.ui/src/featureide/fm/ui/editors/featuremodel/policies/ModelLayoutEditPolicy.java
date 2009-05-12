/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.editors.featuremodel.policies;

import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPolicy;
import org.eclipse.gef.Request;
import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.LayoutEditPolicy;
import org.eclipse.gef.requests.ChangeBoundsRequest;
import org.eclipse.gef.requests.CreateRequest;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.FeatureUIHelper;
import featureide.fm.ui.editors.featuremodel.commands.FeatureDragAndDropCommand;
import featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Allows features to be moved onto the feature model diagram.
 * 
 * @author Thomas Thuem
 */
public class ModelLayoutEditPolicy extends LayoutEditPolicy {

	private final FeatureModel featureModel;

	private FeatureDragAndDropCommand cmd;
	
	public ModelLayoutEditPolicy(FeatureModel featureModel) {
		super();
		this.featureModel = featureModel;
	}

	@Override
	protected EditPolicy createChildEditPolicy(EditPart child) {
		if (child instanceof FeatureEditPart)
			return new FeatureMoveEditPolicy((FeatureEditPart) child, this);
		return null;
	}
	
	@Override
	protected Command getMoveChildrenCommand(Request request) {
		cmd = null;
		if (request instanceof ChangeBoundsRequest) {
			ChangeBoundsRequest r = (ChangeBoundsRequest) request;
			if (r.getEditParts().size() != 1)
				return null;
			FeatureEditPart editPart = (FeatureEditPart) r.getEditParts().get(0);
			Feature feature = editPart.getFeatureModel();
			Rectangle bounds = FeatureUIHelper.getBounds(feature);
			bounds = r.getTransformedRectangle(bounds);
			cmd = new FeatureDragAndDropCommand(featureModel, feature, bounds.getLocation());
		}
		return cmd;
	}

	public FeatureDragAndDropCommand getConstraintCommand() {
		return cmd;
	}

	@Override
	protected Command getCreateCommand(CreateRequest request) {
		//no creation supported
		return null;
	}

}
