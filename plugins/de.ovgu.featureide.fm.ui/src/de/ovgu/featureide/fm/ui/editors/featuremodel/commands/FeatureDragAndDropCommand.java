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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.ObjectUndoContext;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
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

	private final FeatureModel featureModel;

	private final Feature feature;

	private final Point newLocation;

	private final Feature oldParent;

	private final int oldIndex;

	private Feature newParent;

	private int newIndex;
	
	private boolean hasAutoLayout;
	
	private boolean hasVerticalLayout;
	
	private FeatureEditPart editPart;


	public FeatureDragAndDropCommand(FeatureModel featureModel,
			Feature feature, Point newLocation,FeatureEditPart editPart) {
		super("Moving " + feature.getName());
		this.featureModel = featureModel;
		this.feature = feature;
		this.newLocation = newLocation;
		this.hasAutoLayout = featureModel.getLayout().hasFeaturesAutoLayout();
		this.hasVerticalLayout = FeatureUIHelper.hasVerticalLayout(featureModel);
		this.editPart = editPart;
		oldParent = feature.getParent();
		oldIndex = oldParent != null ? oldParent.getChildIndex(feature) : 0;
	}

	@Override
	public boolean canExecute() {
	
		if(hasAutoLayout){
			if(editPart.getSelected()!=2){
				return false;
			}
			Point referencePoint = FeatureUIHelper.getSourceLocation(feature,
					newLocation);
			Feature next = calculateNext(featureModel.getRoot(), referencePoint);

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
			return feature != newParent && !feature.isAncestorOf(newParent);
		}
		return true;
	}

	@Override
	public void execute() {
			FeatureOperationData data = new FeatureOperationData(feature,
					oldParent, newParent, newIndex, oldIndex);
			FeatureMoveOperation op = new FeatureMoveOperation(data, featureModel, newLocation, 
					FeatureUIHelper.getLocation(feature).getCopy(), feature);
			op.addContext((ObjectUndoContext) featureModel.getUndoContext());

			try {
				PlatformUI.getWorkbench().getOperationSupport()
						.getOperationHistory().execute(op, null, null);
			} catch (ExecutionException e) {
				FMUIPlugin.getDefault().logError(e);

			}
	}

	private boolean calculateNewParentAndIndex(Feature next) {
		Point location = FeatureUIHelper
				.getSourceLocation(feature, newLocation);
		Point nextLocation = FeatureUIHelper.getTargetLocation(next);
		Dimension d = location.getDifference(nextLocation);
		if(!hasVerticalLayout){
			if (d.height > 0) {
				// insert below
				newParent = next;
				newIndex = 0;
				for (Feature child : next.getChildren()) {
					Dimension cd = FeatureUIHelper.getSourceLocation(child)
							.getDifference(nextLocation);
					if (d.width / (double) d.height <= cd.width
							/ (double) cd.height)
						break;
					else
						newIndex++;
				}
			} else {
				// insert left or right
				if (next.isRoot()) {
					// do not accept because root has no parent
					return false;
				} else {
					newParent = next.getParent();
					if (d.width < 0)
						newIndex = newParent.getChildIndex(next);
					else
						newIndex = newParent.getChildIndex(next) + 1;
				}
			}

			if (newParent == oldParent
					&& oldParent.getChildIndex(feature) < newIndex)
				newIndex--;

			return true;
		} else {
			if (d.width > 0) {
				// insert below
				newParent = next;
				newIndex = 0;
				for (Feature child : next.getChildren()) {
					Dimension cd = FeatureUIHelper.getSourceLocation(child)
							.getDifference(nextLocation);
					if (d.height / (double) d.width <= cd.height
							/ (double) cd.width)
						break;
					else
						newIndex++;
				}
			} else {
				// insert left or right
				if (next.isRoot()) {
					// do not accept because root has no parent
					return false;
				} else {
					newParent = next.getParent();
					if (d.height < 0)
						newIndex = newParent.getChildIndex(next);
					else
						newIndex = newParent.getChildIndex(next) + 1;
				}
			}

			if (newParent == oldParent
					&& oldParent.getChildIndex(feature) < newIndex)
				newIndex--;

			return true;
		}
		
	}

	public static Feature calculateNext(Feature feature, Point referencePoint) {
		if (feature == null)
			return null;
		Feature next = feature;
		double distance = FeatureUIHelper.getTargetLocation(next).getDistance(
				referencePoint);
		for (Feature child : feature.getChildren()) {
			Feature childsNext = calculateNext(child, referencePoint);
			double newDistance = FeatureUIHelper.getTargetLocation(childsNext)
					.getDistance(referencePoint);
			if (newDistance > 0 && newDistance < distance) {
				next = childsNext;
				distance = newDistance;
			}
		}
		return next;
	}

	public Feature getFeature() {
		return feature;
	}

	public Feature getNewParent() {
	
		return newParent;
	}

}
