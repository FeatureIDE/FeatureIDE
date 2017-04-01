/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Calculates locations for all features in the feature diagram.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
abstract public class FeatureDiagramLayoutManager {

	protected int controlWidth = 10;
	protected int controlHeight = 10;
	protected boolean showHidden, showCollapsedConstraints;

	public final void layout(IGraphicalFeatureModel featureModel) {
		showHidden = featureModel.getLayout().showHiddenFeatures();
		FeatureUIHelper.showHiddenFeatures(showHidden, featureModel);
		showCollapsedConstraints = featureModel.getLayout().showCollapsedConstraints();
		FeatureUIHelper.showCollapsedConstraints(showCollapsedConstraints, featureModel);
		layoutFeatureModel(featureModel);
		for (Entry<IGraphicalFeature, Point> entry : newLocations.entrySet()) {
			entry.getKey().setLocation(entry.getValue());
		}
		if (!FMPropertyManager.isLegendHidden() && featureModel.getLayout().hasLegendAutoLayout()) {
			layoutLegend(featureModel, showHidden);
		}
		newLocations.clear();
	}

	/**
	 * check if feature (or any parent) is hidden
	 */
	boolean isHidden(IGraphicalFeature feature) {
		if (showHidden)
			return false;
		if (!feature.getObject().getStructure().isRoot())
			return (feature.getObject().getStructure().isHidden() || isHidden(FeatureUIHelper.getGraphicalParent(feature)));
		else
			return feature.getObject().getStructure().isHidden();
	}

	protected abstract void layoutFeatureModel(IGraphicalFeatureModel featureModel);

	public void setControlSize(int width, int height) {
		this.controlWidth = width;
		this.controlHeight = height;
	}

	/**
	 * method to center the layout on the screen (horizontal only)
	 */
	@Deprecated
	void centerLayoutX(IGraphicalFeatureModel featureModel) {
		int mostRightFeatureX = Integer.MIN_VALUE;
		int mostLeftFeatureX = Integer.MAX_VALUE;
		for (IGraphicalFeature feature : featureModel.getVisibleFeatures()) {
			int tempX = feature.getLocation().x;
			int tempXOffset = feature.getSize().width;
			if (mostRightFeatureX < tempX + tempXOffset)
				mostRightFeatureX = tempX + tempXOffset;
			if (mostLeftFeatureX > tempX)
				mostLeftFeatureX = tempX;
		}
		int width = mostRightFeatureX - mostLeftFeatureX;
		int offset = mostRightFeatureX - ((controlWidth - width) / 2);
		for (IGraphicalFeature feature : featureModel.getVisibleFeatures()) {
			setLocation(feature, new Point(feature.getLocation().getCopy().x + offset, feature.getLocation().getCopy().y));
		}
	}

	void layout(int yoffset, List<IGraphicalConstraint> constraints) {
		//Added offset to avoid colliding with the collapse decorator
		int y = yoffset + FMPropertyManager.getConstraintSpace() + 20;
		boolean depthFirst = this instanceof DepthFirstLayout;
		for (IGraphicalConstraint constraint : constraints) {
			Dimension size = constraint.getSize();
			int x = depthFirst ? 2 * FMPropertyManager.getFeatureSpaceX() : (controlWidth - size.width) >> 1;
			constraint.setLocation(new Point(x, y));
			y += size.height;
		}
	}

	/**
	 * sets the position of the legend
	 */
	private static void layoutLegend(IGraphicalFeatureModel featureModel, boolean showHidden) {
		final Point min = new Point(Integer.MAX_VALUE, Integer.MAX_VALUE);
		final Point max = new Point(Integer.MIN_VALUE, Integer.MIN_VALUE);

		/*
		 * update lowest, highest, most left, most right coordinates
		 * for features
		 */
		Iterable<IGraphicalFeature> nonHidden = featureModel.getVisibleFeatures();
		for (IGraphicalFeature feature : nonHidden) {
			Rectangle position = FeatureUIHelper.getBounds(feature);
			if (position.x < min.x)
				min.x = position.x;
			if (position.y < min.y)
				min.y = position.y;
			if ((position.x + position.width) > max.x)
				max.x = position.right();
			if (position.y + position.height > max.y)
				max.y = position.bottom();
		}

		/*
		 * update lowest, highest, most left, most right coordinates
		 * for constraints
		 */
		for (IGraphicalConstraint constraint : featureModel.getVisibleConstraints()) {
			Rectangle position = FeatureUIHelper.getBounds(constraint);
			if (position.x < min.x)
				min.x = position.x;
			if (position.y < min.y)
				min.y = position.y;
			if ((position.x + position.width) > max.x)
				max.x = position.right();
			if (position.y + position.height > max.y)
				max.y = position.bottom();
		}

		final Dimension legendSize = FeatureUIHelper.getLegendSize(featureModel);
		if (legendSize == null) {
			return;
		}

		boolean topRight = true;
		boolean topLeft = true;
		boolean botLeft = true;
		boolean botRight = true;

		/*
		 * check if features would intersect with the legend on the edges
		 */
		for (IGraphicalFeature feature : nonHidden) {
			final Point tempLocation = feature.getLocation();
			if (null != tempLocation) {
				final Dimension tempSize = feature.getSize();
				if (tempSize != null) {
					if ((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
							&& (tempLocation.y) < (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY() / 2))
						topRight = false;
					if ((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
							&& (tempLocation.y) < (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY() / 2))
						topLeft = false;
					if ((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
							&& (tempLocation.y + tempSize.height) > (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY() / 2))
						botLeft = false;
					if ((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
							&& (tempLocation.y + tempSize.height) > (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY() / 2))
						botRight = false;
				}
			}
		}
		/*
		 * check if constraints would intersect with the legend on the edges
		 */
		if (topRight || topLeft || botLeft || botRight) {
			for (IGraphicalConstraint constraint : featureModel.getVisibleConstraints()) {
				Point tempLocation = constraint.getLocation();
				if (null == tempLocation)
					continue;
				Dimension tempSize = constraint.getSize();
				if ((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
						&& (tempLocation.y) < (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY() / 2))
					topRight = false;
				if ((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
						&& (tempLocation.y) < (min.y + legendSize.height + FMPropertyManager.getFeatureSpaceY() / 2))
					topLeft = false;
				if ((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX())
						&& (tempLocation.y + tempSize.height) > (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY() / 2))
					botLeft = false;
				if ((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX())
						&& (tempLocation.y + tempSize.height) > (max.y - legendSize.height - FMPropertyManager.getFeatureSpaceY() / 2))
					botRight = false;
			}
		}

		/*
		 * set the legend position
		 */
		if (topRight) {
			featureModel.getLayout().setLegendPos(max.x - legendSize.width, min.y);
		} else if (topLeft) {
			featureModel.getLayout().setLegendPos(min.x, min.y);
		} else if (botLeft) {
			featureModel.getLayout().setLegendPos(min.x, max.y - legendSize.height);
		} else if (botRight) {
			featureModel.getLayout().setLegendPos(max.x - legendSize.width, max.y - legendSize.height);
		} else {
			featureModel.getLayout().setLegendPos(max.x + FMPropertyManager.getFeatureSpaceX(), min.y);
		}
	}

	/**
	 * Stores locations separately to {@link IGraphicalFeature}.
	 */
	protected Map<IGraphicalFeature, Point> newLocations = new HashMap<>();

	protected void setLocation(IGraphicalFeature feature, Point location) {
		newLocations.put(feature, location);
	}

	protected Point getLocation(IGraphicalFeature feature) {
		Point location = newLocations.get(feature);
		if (location == null) {
			location = feature.getLocation();
		}
		return location;
	}

	protected Rectangle getBounds(IGraphicalFeature feature) {
		if (getLocation(feature) == null || feature.getSize() == null) {
			// UIHelper not set up correctly, refresh the feature model
			feature.getObject().getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(getLocation(feature), feature.getSize());
	}

	protected List<IGraphicalFeature> getChildren(IGraphicalFeature feature) {
		return Functional.toList(feature.getGraphicalChildren());
	}
}
