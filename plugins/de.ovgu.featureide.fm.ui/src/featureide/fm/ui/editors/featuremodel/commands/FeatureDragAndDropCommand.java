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
package featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.commands.Command;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.FeatureUIHelper;

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

	public FeatureDragAndDropCommand(FeatureModel featureModel, Feature feature, Point newLocation) {
		super("Moving " + feature.getName());
		this.featureModel = featureModel;
		this.feature = feature;
		this.newLocation = newLocation;
		oldParent = feature.getParent();
		oldIndex = oldParent != null ? oldParent.getChildIndex(feature) : 0;
	}

	@Override
	public boolean canExecute() {
		Point referencePoint = FeatureUIHelper.getSourceLocation(feature,newLocation);
		Feature next = calculateNext(featureModel.getRoot(), referencePoint);
		
		//calculate new parent (if exists)
		if (!calculateNewParentAndIndex(next))
			return false;
	
		//no new positions possible next to same feature
		if (next == feature) 
			return false;
		
		//not accept the same position
		if (oldParent == newParent && oldIndex == newIndex)
			return false;
		
		//not accept leaves as parent
		if (!newParent.canHaveChildren())
			return false;
		
		//not accept moves to children positions
		return feature != newParent && !feature.isAncestorOf(newParent);
	}

	@Override
	public void execute() {
		boolean deleteParent = oldParent.isAbstract() && oldParent.getChildrenCount() == 1;
		oldParent.removeChild(feature);
		newParent.addChildAtPosition(newIndex, feature);
		if (deleteParent)
			featureModel.deleteFeature(oldParent);
		featureModel.handleModelDataChanged();
	}

	@Override
	public void undo() {
		newParent.removeChild(feature);
		//TODO #46: implement undo for deleted compound features 
		if (oldParent != null) 
			oldParent.addChildAtPosition(oldIndex, feature);
		featureModel.handleModelDataChanged();
	}
	
	private boolean calculateNewParentAndIndex(Feature next) {
		Point location = FeatureUIHelper.getSourceLocation(feature,newLocation);
		Point nextLocation = FeatureUIHelper.getTargetLocation(next);
		Dimension d = location.getDifference(nextLocation);
		
//		if (Math.abs(d.width) < d.height) {
		if (d.height > 0) {
			//insert below
			newParent = next;
			newIndex = 0;
			for (Feature child : next.getChildren()) {
				Dimension cd = FeatureUIHelper.getSourceLocation(child).getDifference(nextLocation);
				if (d.width / (double) d.height <= cd.width / (double) cd.height)
					break;
				else
					newIndex++;
			}
		}
		else {
			//insert left or right
			if (next.isRoot()) {
				//do not accept because root has no parent
				return false;
			}
			else {
				newParent = next.getParent();
				if (d.width < 0)
					newIndex = newParent.getChildIndex(next);
				else
					newIndex = newParent.getChildIndex(next) + 1;
			}
		}
		
		if (newParent == oldParent && oldParent.getChildIndex(feature) < newIndex)
			newIndex--;
		
		return true;
	}

	public static Feature calculateNext(Feature feature, Point referencePoint) {
		if (feature == null)
			return null;
		Feature next = feature;
		double distance = FeatureUIHelper.getTargetLocation(next).getDistance(referencePoint);
		for (Feature child : feature.getChildren()) {
			Feature childsNext = calculateNext(child, referencePoint);
			double newDistance = FeatureUIHelper.getTargetLocation(childsNext).getDistance(referencePoint);
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
