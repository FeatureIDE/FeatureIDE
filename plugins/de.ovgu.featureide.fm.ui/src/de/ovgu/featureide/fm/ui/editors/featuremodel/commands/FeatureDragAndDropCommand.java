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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.commands.Command;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureOperationData;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.MoveFeatureOperation;

/**
 * This command allows the user to move features at the feature diagram using drag and drop.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureDragAndDropCommand extends Command {

	private final IGraphicalFeatureModel featureModel;

	private final IGraphicalFeature feature;

	private final Point newLocation;

	private final IGraphicalFeature oldParent;

	private final int oldIndex;

	private IGraphicalFeature newParent;

	private int newIndex;

	private final boolean hasAutoLayout;

	private final boolean hasVerticalLayout;

	private final FeatureEditPart editPart;

	public FeatureDragAndDropCommand(IGraphicalFeatureModel featureModel, IGraphicalFeature feature, Point newLocation, FeatureEditPart editPart) {
		super("Moving " + feature.getObject().getName());
		this.featureModel = featureModel;
		this.feature = feature;
		this.newLocation = newLocation;
		hasAutoLayout = featureModel.getLayout().hasFeaturesAutoLayout();
		hasVerticalLayout = FeatureUIHelper.hasVerticalLayout(featureModel);
		this.editPart = editPart;
		oldParent = FeatureUIHelper.getGraphicalParent(feature);
		oldIndex = oldParent != null ? FeatureUIHelper.getGraphicalChildren(oldParent).indexOf(feature) : 0;
	}

	@Override
	public boolean canExecute() {
		if (hasAutoLayout) {
			if (editPart.getSelected() != 2) {
				return false;
			}
			final Point referencePoint = FeatureUIHelper.getSourceLocation(feature, newLocation);
			final IGraphicalFeature next = calculateNext(referencePoint);
			if (next == null) {
				return false;
			}

			// calculate new parent (if exists)
			if (!calculateNewParentAndIndex(next)) {
				return false;
			}

			// no new positions possible next to same feature
			if (next == feature) {
				return false;
			}

			// not accept the same position
			if ((oldParent == newParent) && (oldIndex == newIndex)) {
				return false;
			}

			// not accept moves to children positions
			if (feature == newParent) {
				return false;
			}

			if (FeatureUIHelper.isAncestorOf(newParent, feature)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public void execute() {
		final FeatureOperationData data = new FeatureOperationData(feature, oldParent, newParent, newIndex, oldIndex);
		final MoveFeatureOperation op = new MoveFeatureOperation(data, editPart.getViewer(), newLocation, feature.getLocation().getCopy(), feature.getObject());
		// TODO _interfaces Removed Code

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

	private boolean calculateNewParentAndIndex(IGraphicalFeature next) {
		final Point location = FeatureUIHelper.getSourceLocation(feature, newLocation);
		final Point nextLocation = FeatureUIHelper.getTargetLocation(next);
		final Dimension d = location.getDifference(nextLocation);
		if (!hasVerticalLayout) {
			if (d.height > 0) {
				// insert below
				newParent = next;
				newIndex = 0;
				for (final IGraphicalFeature child : FeatureUIHelper.getGraphicalChildren(next)) {
					final Dimension cd = FeatureUIHelper.getSourceLocation(child).getDifference(nextLocation);
					if ((d.width / (double) d.height) <= (cd.width / (double) cd.height)) {
						break;
					} else {
						newIndex++;
					}
				}
			} else {
				// insert left or right
				if (next.getObject().getStructure().isRoot()) {
					// do not accept because root has no parent
					return false;
				} else {
					newParent = FeatureUIHelper.getGraphicalParent(next);
					if (d.width < 0) {
						newIndex = FeatureUIHelper.getGraphicalChildren(newParent).indexOf(next);
					} else {
						newIndex = FeatureUIHelper.getGraphicalChildren(newParent).indexOf(next) + 1;
					}
				}
			}

			if ((newParent == oldParent) && (FeatureUIHelper.getGraphicalChildren(oldParent).indexOf(feature) < newIndex)) {
				newIndex--;
			}

			return true;
		} else {
			if (d.width > 0) {
				// insert below
				newParent = next;
				newIndex = 0;
				for (final IGraphicalFeature child : FeatureUIHelper.getGraphicalChildren(next)) {
					final Dimension cd = FeatureUIHelper.getSourceLocation(child).getDifference(nextLocation);
					if ((d.height / (double) d.width) <= (cd.height / (double) cd.width)) {
						break;
					} else {
						newIndex++;
					}
				}
			} else {
				// insert left or right
				if (next.getObject().getStructure().isRoot()) {
					// do not accept because root has no parent
					return false;
				} else {
					newParent = FeatureUIHelper.getGraphicalParent(next);
					if (d.height < 0) {
						newIndex = FeatureUIHelper.getGraphicalChildren(newParent).indexOf(next);
					} else {
						newIndex = FeatureUIHelper.getGraphicalChildren(newParent).indexOf(next) + 1;
					}
				}
			}

			if ((newParent == oldParent) && (FeatureUIHelper.getGraphicalChildren(oldParent).indexOf(feature) < newIndex)) {
				newIndex--;
			}

			return true;
		}

	}

	public IGraphicalFeature calculateNext(final Point referencePoint) {
		IGraphicalFeature next = null;
		int distance = Integer.MAX_VALUE;
		for (final IGraphicalFeature child : featureModel.getVisibleFeatures()) {
			final Point targetLocation = FeatureUIHelper.getTargetLocation(child);
			if ((hasVerticalLayout && (targetLocation.x < referencePoint.x)) || (!hasVerticalLayout && (targetLocation.y < referencePoint.y))) {
				final int newDistance = (int) targetLocation.getDistance(referencePoint);
				if ((newDistance > 0) && (newDistance < distance)) {
					next = child;
					distance = newDistance;
				}
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
