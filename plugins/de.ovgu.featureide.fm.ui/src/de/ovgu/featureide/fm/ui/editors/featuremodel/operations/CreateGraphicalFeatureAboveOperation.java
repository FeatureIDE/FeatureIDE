/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to create a compound feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class CreateGraphicalFeatureAboveOperation extends AbstractGraphicalFeatureModelOperation {

	private static final int topDownDefaultDistance = 50;
	private static final int leftRightDefaultDistance = 120;

	private final LinkedList<String> selectedFeatureNames;

	private String newFeatureName;
	private int distance;

	public CreateGraphicalFeatureAboveOperation(IGraphicalFeatureModel graphicalFeatureModel, LinkedList<String> selectedFeatures) {
		super(graphicalFeatureModel, "Create Feature Above");
		selectedFeatureNames = selectedFeatures;
	}

	/**
	 * adjusts position of the new feature and its children in manual layout
	 */
	private void adjustPositions(IGraphicalFeature newGraphicalFeature) {
		final List<IGraphicalFeature> graphicalChildren = newGraphicalFeature.getGraphicalChildren();
		int minX = graphicalChildren.get(0).getLocation().x;
		int minY = graphicalChildren.get(0).getLocation().y;
		int yLocation = graphicalChildren.get(0).getLocation().y;
		int xLocation = graphicalChildren.get(0).getLocation().x;

		// looks for the leftest x coordinate and the topmost y coordinate of a child
		for (final IGraphicalFeature child : graphicalChildren) {
			if (child.getLocation().x < minX) {
				minX = child.getLocation().x;
				yLocation = child.getLocation().y;
			}
			if (child.getLocation().y < minY) {
				minY = child.getLocation().y;
				xLocation = child.getLocation().x;
			}
		}

		// decides if the anchor points are at the side or on the top of the rectangle
		int distance;
		boolean topDown;
		if (!newGraphicalFeature.getGraphicalModel().getLayout().hasVerticalLayout()) {
			newGraphicalFeature.setLocation(new Point(minX, yLocation));
			topDown = true;
			distance = topDownDefaultDistance;
		} else {
			newGraphicalFeature.setLocation(new Point(xLocation, minY));
			topDown = false;
			distance = leftRightDefaultDistance;
		}
		this.distance = distance;
		shiftChildren(graphicalChildren, distance, topDown);
	}

	/**
	 * shifts the subtree of the new feature above
	 *
	 * @param graphicalChildren children of the new feature
	 * @param distance distance to shift
	 * @param topDown previous layout
	 */
	private void shiftChildren(List<IGraphicalFeature> graphicalChildren, int distance, boolean topDown) {
		for (int i = 0; i < graphicalChildren.size(); i++) {
			shiftChildren(graphicalChildren.get(i).getGraphicalChildren(), distance, topDown);
			// if there are more layouts to come, there has to be more cases added here
			if (topDown) {
				graphicalChildren.get(i).setLocation(new Point(graphicalChildren.get(i).getLocation().x, graphicalChildren.get(i).getLocation().y + distance));
			} else {
				graphicalChildren.get(i).setLocation(new Point(graphicalChildren.get(i).getLocation().x + distance, graphicalChildren.get(i).getLocation().y));
			}
		}
	}

	private CreateFeatureAboveOperation createFeatureOperation;

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		createFeatureOperation = new CreateFeatureAboveOperation(featureModelManager, selectedFeatureNames);
		final FeatureIDEEvent event = createFeatureOperation.operation(featureModel);
		if (event != null) {
			final IFeature newFeature = (IFeature) event.getNewValue();
			newFeatureName = newFeature.getName();
			// checks if manual layout is chosen
			if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
				adjustPositions(graphicalFeatureModel.getGraphicalFeature(newFeature));
			}
			return event;
		}
		return null;
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (newFeatureName != null) {
			if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
				final IGraphicalFeature newGraphicalFeature = graphicalFeatureModel.getGraphicalFeature(featureModel.getFeature(newFeatureName));
				shiftChildren(newGraphicalFeature.getGraphicalChildren(), (-distance), !graphicalFeatureModel.getLayout().hasVerticalLayout());
			}
			return createFeatureOperation.inverseOperation(featureModel);
		}
		return null;
	}

	@Override
	protected int getChangeIndicator() {
		// The operation creates features internally => change indicator to CHANGE_DEPENDENCIES
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}
}
