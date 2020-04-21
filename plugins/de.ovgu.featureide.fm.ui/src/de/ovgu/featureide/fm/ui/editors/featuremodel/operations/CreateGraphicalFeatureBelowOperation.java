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

import java.util.List;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to create a layer feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Sebastian Krieter
 */
public class CreateGraphicalFeatureBelowOperation extends AbstractGraphicalFeatureModelOperation {

	private static final int xDistanceTopDown = 5;
	private static final int yDistanceTopDown = 31;
	private static final int xDistanceLeftRight = 20;
	private static final int yDistanceLeftRight = 8;

	private final String parentName;

	private CreateFeatureOperation createFeatureOperation;

	public CreateGraphicalFeatureBelowOperation(String parentName, IGraphicalFeatureModel featureModel) {
		super(featureModel, "Create Feature Below");
		this.parentName = parentName;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature parent = featureModel.getFeature(parentName);
		if (parent != null) {
			createFeatureOperation = new CreateFeatureOperation(parent.getName(), parent.getStructure().getChildrenCount(), featureModelManager);
			final FeatureIDEEvent event = createFeatureOperation.operation(featureModel);
			if (event != null) {
				final IFeature newFeature = (IFeature) event.getNewValue();
				// checks if manual layout is chosen
				if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
					final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(parent);
					int maxX = graphicalFeature.getLocation().x - xDistanceTopDown;
					int maxY = graphicalFeature.getLocation().y - yDistanceLeftRight;
					int yLocation = graphicalFeature.getLocation().y() + yDistanceTopDown + graphicalFeature.getSize().height;
					int xLocation = graphicalFeature.getLocation().x + xDistanceLeftRight + graphicalFeature.getSize().width;
					final List<IGraphicalFeature> olderSiblings = graphicalFeature.getGraphicalChildren();

					if (olderSiblings.size() != 1) {
						// looks for the most right x coordinate and the lowest y coordinate of a child
						for (int i = 0; i < olderSiblings.size(); i++) {
							final int rightFeatureBorder = (olderSiblings.get(i).getLocation().x + olderSiblings.get(i).getSize().width);
							final int downFeatureBorder = (olderSiblings.get(i).getLocation().y + olderSiblings.get(i).getSize().height);
							if (rightFeatureBorder >= maxX) {
								maxX = rightFeatureBorder;
								yLocation = olderSiblings.get(i).getLocation().y;
							}
							if (downFeatureBorder >= maxY) {
								maxY = downFeatureBorder;
								xLocation = olderSiblings.get(i).getLocation().x;
							}
						}
					}
					// decides if the anchor points are at the side or on the top of the rectangle
					if (!graphicalFeatureModel.getLayout().hasVerticalLayout()) {
						graphicalFeatureModel.getGraphicalFeature(newFeature).setLocation(new Point(maxX + xDistanceTopDown, yLocation));
					} else {
						graphicalFeatureModel.getGraphicalFeature(newFeature).setLocation(new Point(xLocation, maxY + yDistanceLeftRight));
					}
				}
				return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD, parent != null ? parent : null, newFeature);
			}
		}
		return null;
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		return createFeatureOperation != null ? createFeatureOperation.inverseOperation(featureModel) : null;
	}

	@Override
	protected int getChangeIndicator() {
		// The operation creates features internally => change indicator to CHANGE_DEPENDENCIES
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
