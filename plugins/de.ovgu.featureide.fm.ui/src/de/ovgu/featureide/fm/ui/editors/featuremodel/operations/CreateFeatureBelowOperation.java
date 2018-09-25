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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_LAYER;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_FEATURE_LAYER_CAPTION;

import java.util.List;

import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;

/**
 * Operation with functionality to create a layer feature. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Sebastian Krieter
 */
public class CreateFeatureBelowOperation extends AbstractFeatureModelOperation {

	private IFeature feature;
	private IFeature newFeature;
	private final IGraphicalFeature graphicalFeature;
	private IGraphicalFeature newGraphicalFeature;
	private final int xDistanceTopDown = 5;
	private final int yDistanceTopDown = 31;
	private final int xDistanceLeftRight = 20;
	private final int yDistanceLeftRight = 8;

	public CreateFeatureBelowOperation(IGraphicalFeature feature, IFeatureModel featureModel) {
		super(featureModel, CREATE_LAYER);
		this.feature = feature.getObject();
		graphicalFeature = feature;
	}

	@Override
	protected FeatureIDEEvent operation() {
		int number = 1;

		while (FeatureUtils.getFeatureNames(featureModel).contains(DEFAULT_FEATURE_LAYER_CAPTION + number)) {
			number++;
		}

		newFeature = FMFactoryManager.getFactory(featureModel).createFeature(featureModel, DEFAULT_FEATURE_LAYER_CAPTION + number);
		featureModel.addFeature(newFeature);
		feature = featureModel.getFeature(feature.getName());
		feature.getStructure().addChild(newFeature.getStructure());

		newGraphicalFeature = graphicalFeature.getGraphicalModel().getGraphicalFeature(newFeature);

		if (graphicalFeature.getGraphicalModel().getLayout().getLayoutAlgorithm() == 0) {
			setNewPositionFeatureBelow();
		}

		return new FeatureIDEEvent(featureModel, EventType.FEATURE_ADD, feature, newFeature);
	}

	/**
	 * adjust position of the new feature in manual layout
	 */
	private void setNewPositionFeatureBelow() {
		int maxX = graphicalFeature.getLocation().x - xDistanceTopDown;
		int maxY = graphicalFeature.getLocation().y - yDistanceLeftRight;
		int yLocation = graphicalFeature.getLocation().y() + yDistanceTopDown + graphicalFeature.getSize().height;
		int xLocation = graphicalFeature.getLocation().x + xDistanceLeftRight + graphicalFeature.getSize().width;
		final List<IGraphicalFeature> olderSiblings = graphicalFeature.getGraphicalChildren(true);

		if (olderSiblings.size() != 1) {
			// looks for the rightest x coordinate and the lowermost y coordinate of a child
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
		if (!newGraphicalFeature.getGraphicalModel().getLayout().verticalLayout()) {
			newGraphicalFeature.setLocation(new Point(maxX + xDistanceTopDown, yLocation));
		} else {
			newGraphicalFeature.setLocation(new Point(xLocation, maxY + yDistanceLeftRight));
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		newFeature = featureModel.getFeature(newFeature.getName());
		featureModel.deleteFeature(newFeature);
		return new FeatureIDEEvent(newFeature, EventType.FEATURE_DELETE, null, newFeature);
	}
}
