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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.List;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.filter.base.IFilter;
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
 */
abstract public class FeatureDiagramLayoutManager {
	
	protected static final class HiddenFilter implements IFilter<IGraphicalFeature> {
		@Override
		public boolean isValid(IGraphicalFeature object) {
			return !object.getObject().getStructure().isHidden();
		}
	}

	protected int controlWidth = 10;
	protected int controlHeight = 10;
	protected boolean showHidden;

	public void layout(IGraphicalFeatureModel featureModel) {
		showHidden = featureModel.getLayout().showHiddenFeatures();
		FeatureUIHelper.showHiddenFeatures(showHidden, featureModel);
		layoutFeatureModel(featureModel);
		if (!FMPropertyManager.isLegendHidden() && featureModel.getLayout().hasLegendAutoLayout()) {
			layoutLegend(featureModel, showHidden);
		}
		layoutHidden(featureModel);
	}

	/**
	 * check if feature (or any parent) is hidden
	 */
	boolean isHidden(IGraphicalFeature feature) {
		if (showHidden)
			return false;
		if (!feature.getObject().getStructure().isRoot())
			return (feature.getObject().getStructure().isHidden() || isHidden(feature.getTree().getParentObject()));
		else
			return feature.getObject().getStructure().isHidden();
	}

	/**
	 * the location of hidden features is set to (0,0) temporary
	 * (not the position that is saved in model.xml)
	 */
	void layoutHidden(IGraphicalFeatureModel featureModel) {
		for (IGraphicalFeature feature : featureModel.getFeatures()) {
			if (isHidden(feature) && !feature.getObject().getStructure().isRoot()) {
				FeatureUIHelper.setTemporaryLocation(feature, new Point(0, 0));
			}
		}
	}

	abstract public void layoutFeatureModel(IGraphicalFeatureModel featureModel);

	public void setControlSize(int width, int height) {
		this.controlWidth = width;
		this.controlHeight = height;
	}

	/**
	 * method to center the layout on the screen (horizontal only)
	 */
	void centerLayoutX(IGraphicalFeatureModel featureModel) {
		int mostRightFeatureX = Integer.MIN_VALUE;
		int mostLeftFeatureX = Integer.MAX_VALUE;
		for (IGraphicalFeature feature : featureModel.getFeatures()) {
			int tempX = FeatureUIHelper.getLocation(feature).x;
			int tempXOffset = FeatureUIHelper.getSize(feature).width;
			if (mostRightFeatureX < tempX + tempXOffset)
				mostRightFeatureX = tempX + tempXOffset;
			if (mostLeftFeatureX > tempX)
				mostLeftFeatureX = tempX;
		}
		int width = mostRightFeatureX - mostLeftFeatureX;
		int offset = mostRightFeatureX - ((controlWidth - width) / 2);
		for (IGraphicalFeature feature : featureModel.getFeatures()) {
			FeatureUIHelper.setLocation(feature, new Point(FeatureUIHelper.getLocation(feature).getCopy().x + offset, FeatureUIHelper.getLocation(feature)
					.getCopy().y));
		}
	}

	void layout(int yoffset, List<IGraphicalConstraint> constraints) {
		int y = yoffset + FMPropertyManager.getConstraintSpace();
		boolean depthFirst = this instanceof DepthFirstLayout;
		for (IGraphicalConstraint constraint : constraints) {
			Dimension size = FeatureUIHelper.getSize(constraint);
			int x = depthFirst ? 2 * FMPropertyManager.getFeatureSpaceX() : (controlWidth - size.width) >> 1;
			FeatureUIHelper.setLocation(constraint, new Point(x, y));
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
		Iterable<IGraphicalFeature> nonHidden = showHidden ? featureModel.getFeatures() : Functional.filter(featureModel.getFeatures(), new HiddenFilter());
		for (IGraphicalFeature feature : nonHidden) {
			Point temp = FeatureUIHelper.getLocation(feature);
			if (null == temp)
				continue;
			Dimension tempSize = FeatureUIHelper.getSize(feature);

			if (temp.x < min.x)
				min.x = temp.x;
			if (temp.y < min.y)
				min.y = temp.y;
			if ((temp.x + tempSize.width) > max.x)
				max.x = temp.x + tempSize.width;
			if (temp.y + tempSize.height > max.y)
				max.y = temp.y + tempSize.height;
		}

		/*
		 * update lowest, highest, most left, most right coordinates
		 * for constraints
		 */
		for (IGraphicalConstraint constraint : featureModel.getConstraints()) {
			Point temp = FeatureUIHelper.getLocation(constraint);
			if (null == temp)
				continue;
			Dimension tempSize = FeatureUIHelper.getSize(constraint);
			if (temp.x < min.x)
				min.x = temp.x;
			if (temp.y < min.y)
				min.y = temp.y;
			if ((temp.x + tempSize.width) > max.x)
				max.x = temp.x + tempSize.width;
			if (temp.y + tempSize.height > max.y)
				max.y = temp.y + tempSize.height;
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
			final Point tempLocation = FeatureUIHelper.getLocation(feature);
			if (null != tempLocation) {
				final Dimension tempSize = FeatureUIHelper.getSize(feature);
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
			for (IGraphicalConstraint constraint : featureModel.getConstraints()) {
				Point tempLocation = FeatureUIHelper.getLocation(constraint);
				if (null == tempLocation)
					continue;
				Dimension tempSize = FeatureUIHelper.getSize(constraint);
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
}
