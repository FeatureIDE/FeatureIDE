/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureMoveOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureOperationData;

/**
 * This command allows the user to move features at the feature diagram using
 * drag and drop.
 * 
 * @author Thomas Thuem
 */
public class FeatureDragAndDropCommand extends Command {

	private final IGraphicalFeatureModel featureModel;

	private final IGraphicalFeature feature;

	private final Point newLocation;

	private final IGraphicalFeature oldParent;

	private final int oldIndex;

	private IGraphicalFeature newParent;

	private int newIndex;

	private boolean hasAutoLayout;

	private boolean hasVerticalLayout;

	private FeatureEditPart editPart;

	public FeatureDragAndDropCommand(IGraphicalFeatureModel featureModel, IGraphicalFeature feature, Point newLocation, FeatureEditPart editPart) {
		super("Moving " + feature.getObject().getName());
		this.featureModel = featureModel;
		this.feature = feature;
		this.newLocation = newLocation;
		this.hasAutoLayout = featureModel.getLayout().hasFeaturesAutoLayout();
		this.hasVerticalLayout = FeatureUIHelper.hasVerticalLayout(featureModel);
		this.editPart = editPart;
		oldParent = feature.getTree().getParentObject();
		oldIndex = oldParent != null ? oldParent.getTree().getChildren().indexOf(feature.getTree()) : 0;
	}

	@Override
	public boolean canExecute() {

		if (hasAutoLayout) {
			if (editPart.getSelected() != 2) {
				return false;
			}
			Point referencePoint = FeatureUIHelper.getSourceLocation(feature, newLocation);
			IGraphicalFeature next = calculateNext(featureModel.getFeatures().getObject(), referencePoint);

			// calculate new parent (if exists)
			if (!calculateNewParentAndIndex(next))
				return false;

			// no new positions possible next to same feature
			if (next == feature)
				return false;

			// not accept the same position
			if (oldParent == newParent && oldIndex == newIndex)
				return false;

			// not accept moves to children positions
			return feature != newParent && !feature.getTree().isAncestorOf(newParent.getTree());
		}
		return true;
	}

	@Override
	public void execute() {
		FeatureOperationData data = new FeatureOperationData(feature, oldParent, newParent, newIndex, oldIndex);
		FeatureMoveOperation op = new FeatureMoveOperation(data, editPart.getViewer(), newLocation, FeatureUIHelper.getLocation(feature).getCopy(), feature.getObject());
		//TODO _interfaces Removed Code
		op.addContext((ObjectUndoContext) featureModel.getFeatureModel().getUndoContext());


		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

	private boolean calculateNewParentAndIndex(IGraphicalFeature next) {
		Point location = FeatureUIHelper.getSourceLocation(feature, newLocation);
		Point nextLocation = FeatureUIHelper.getTargetLocation(next);
		Dimension d = location.getDifference(nextLocation);
		if (!hasVerticalLayout) {
			if (d.height > 0) {
				// insert below
				newParent = next;
				newIndex = 0;
				for (IGraphicalFeature child : next.getTree().getChildrenObjects()) {
					Dimension cd = FeatureUIHelper.getSourceLocation(child).getDifference(nextLocation);
					if (d.width / (double) d.height <= cd.width / (double) cd.height)
						break;
					else
						newIndex++;
				}
			} else {
				// insert left or right
				if (next.getTree().isRoot()) {
					// do not accept because root has no parent
					return false;
				} else {
					newParent = next.getTree().getParentObject();
					if (d.width < 0)
						newIndex = newParent.getTree().getChildren().indexOf(next.getTree());
					else
						newIndex = newParent.getTree().getChildren().indexOf(next.getTree()) + 1;
				}
			}

			if (newParent == oldParent && oldParent.getTree().getChildren().indexOf(feature.getTree()) < newIndex)
				newIndex--;

			return true;
		} else {
			if (d.width > 0) {
				// insert below
				newParent = next;
				newIndex = 0;
				for (IGraphicalFeature child : next.getTree().getChildrenObjects()) {
					Dimension cd = FeatureUIHelper.getSourceLocation(child).getDifference(nextLocation);
					if (d.height / (double) d.width <= cd.height / (double) cd.width)
						break;
					else
						newIndex++;
				}
			} else {
				// insert left or right
				if (next.getTree().isRoot()) {
					// do not accept because root has no parent
					return false;
				} else {
					newParent = next.getTree().getParentObject();
					if (d.height < 0)
						newIndex = newParent.getTree().getChildren().indexOf(next.getTree());
					else
						newIndex = newParent.getTree().getChildren().indexOf(next.getTree()) + 1;
				}
			}

			if (newParent == oldParent && oldParent.getTree().getChildren().indexOf(feature.getTree()) < newIndex)
				newIndex--;

			return true;
		}

	}

	public static IGraphicalFeature calculateNext(IGraphicalFeature feature, Point referencePoint) {
		if (feature == null)
			return null;
		IGraphicalFeature next = feature;
		double distance = FeatureUIHelper.getTargetLocation(next).getDistance(referencePoint);
		for (IGraphicalFeature child : feature.getTree().getChildrenObjects()) {
			IGraphicalFeature childsNext = calculateNext(child, referencePoint);
			double newDistance = FeatureUIHelper.getTargetLocation(childsNext).getDistance(referencePoint);
			if (newDistance > 0 && newDistance < distance) {
				next = childsNext;
				distance = newDistance;
			}
		}
		return next;
	}

	public IGraphicalFeature getFeature() {
		return feature;
	}

	public IGraphicalFeature getNewParent() {
		return newParent;
	}

}
