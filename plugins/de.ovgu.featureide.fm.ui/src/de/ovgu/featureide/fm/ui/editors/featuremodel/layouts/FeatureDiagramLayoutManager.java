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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;

import org.abego.treelayout.Configuration;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalElement;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Calculates locations for all features in the feature diagram.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 * @author Edgard Schmidt
 * @author Stefanie Schober
 * @author Jann-Ole Henningson
 */
abstract public class FeatureDiagramLayoutManager {

	protected int controlWidth = 10;
	protected int controlHeight = 10;
	protected boolean showHidden, showCollapsedConstraints;
	protected ScrollingGraphicalViewer editor;
	private boolean firstManualLayout = false;

	public final void layout(IGraphicalFeatureModel featureModel, ScrollingGraphicalViewer editor) {
		this.editor = editor;
		showHidden = featureModel.getLayout().showHiddenFeatures();
		FeatureUIHelper.showHiddenFeatures(showHidden, featureModel);
		showCollapsedConstraints = featureModel.getLayout().showCollapsedConstraints();
		FeatureUIHelper.showCollapsedConstraints(showCollapsedConstraints, featureModel);
		layoutFeatureModel(featureModel);
		for (final Entry<IGraphicalFeature, Point> entry : newLocations.entrySet()) {
			entry.getKey().setLocation(entry.getValue());
		}
		if ((featureModel.getLayout().getLayoutAlgorithm() == 0) && !firstManualLayout) {
			for (final IGraphicalFeature entry : featureModel.getFeatures()) {
				// Fix of #571: All feature in manual layout are loaded to their position. Because the layout
				// does not change the position no event is performed and the connections are not drawn. So for the first
				// start perform the location changed event to refresh the connection only in manual layout
				entry.update(FeatureIDEEvent.getDefault(EventType.LOCATION_CHANGED));
				firstManualLayout = true;
			}
		}

		if (!featureModel.isLegendHidden()) {
			if (featureModel.getLayout().hasLegendAutoLayout()) {
				layoutLegend(featureModel);
			}
		}
		newLocations.clear();
	}

	/**
	 * check if feature (or any parent) is hidden
	 */
	boolean isHidden(IGraphicalFeature feature) {
		if (showHidden) {
			return false;
		}
		if (!feature.getObject().getStructure().isRoot()) {
			return (feature.getObject().getStructure().isHidden() || isHidden(FeatureUIHelper.getGraphicalParent(feature)));
		} else {
			return feature.getObject().getStructure().isHidden();
		}
	}

	protected abstract void layoutFeatureModel(IGraphicalFeatureModel featureModel);

	public void setControlSize(int width, int height) {
		controlWidth = width;
		controlHeight = height;
	}

	/**
	 * method to center the layout on the screen (horizontal only)
	 */
	@Deprecated
	void centerLayoutX(IGraphicalFeatureModel featureModel) {
		int mostRightFeatureX = Integer.MIN_VALUE;
		int mostLeftFeatureX = Integer.MAX_VALUE;
		for (final IGraphicalFeature feature : featureModel.getVisibleFeatures()) {
			final int tempX = feature.getLocation().x;
			final int tempXOffset = feature.getSize().width;
			if (mostRightFeatureX < (tempX + tempXOffset)) {
				mostRightFeatureX = tempX + tempXOffset;
			}
			if (mostLeftFeatureX > tempX) {
				mostLeftFeatureX = tempX;
			}
		}
		final int width = mostRightFeatureX - mostLeftFeatureX;
		final int offset = mostRightFeatureX - ((controlWidth - width) / 2);
		for (final IGraphicalFeature feature : featureModel.getVisibleFeatures()) {
			setLocation(feature, new Point(feature.getLocation().getCopy().x + offset, feature.getLocation().getCopy().y));
		}
	}

	void layoutConstraints(int yoffset, List<IGraphicalConstraint> constraints, Rectangle rootBounds) {
		// added 2 times getConstraintSpace to prevent intersecting with the collapsed decorator
		int y = yoffset + (FMPropertyManager.getConstraintSpace() * 2);
		final boolean depthFirst = (this instanceof DepthFirstLayout) || (this instanceof VerticalLayout);
		for (final IGraphicalConstraint constraint : constraints) {
			final Dimension size = constraint.getSize();
			int x;
			if (depthFirst || (constraint.getGraphicalModel().getLayout().getAbegoRootposition() == Configuration.Location.Left)) {
				if (depthFirst) {
					x = 2 * FMPropertyManager.getFeatureSpaceX();
				} else {
					x = rootBounds.x;
				}
			} else if (constraint.getGraphicalModel().getLayout().getAbegoRootposition() == Configuration.Location.Right) {
				final int rootRight = rootBounds.x + rootBounds.width;
				x = rootRight - size.width;
			} else {
				final int rootCenter = rootBounds.x + (rootBounds.width / 2);
				x = rootCenter - (size.width / 2);
			}
			constraint.setLocation(new Point(x, y));

			y += size.height;
		}
	}

	public Rectangle getFeatureModelBounds(List<? extends IGraphicalElement> elements) {
		final Point min = new Point(Integer.MAX_VALUE, Integer.MAX_VALUE);
		final Point max = new Point(Integer.MIN_VALUE, Integer.MIN_VALUE);

		/*
		 * update lowest, highest, most left, most right coordinates for elements
		 */

		for (final IGraphicalElement element : elements) {
			final Rectangle position = FeatureUIHelper.getBounds(element);
			if (position.x < min.x) {
				min.x = position.x;
			}
			if (position.y < min.y) {
				min.y = position.y;
			}
			if ((position.x + position.width) > max.x) {
				max.x = position.right();
			}
			if ((position.y + position.height) > max.y) {
				max.y = position.bottom();
			}
		}

		return new Rectangle(min, max);
	}

	/**
	 * Checks whether the passed rectangle is crossed by a line in between source and target
	 *
	 * @param source
	 * @param target
	 * @param rect
	 * @return is there an intersection?
	 */
	public boolean rectangleConnectionIntersection(Point source, Point target, Rectangle rect) {
		final Point min = rect.getTopLeft();
		final Point max = rect.getBottomRight();

		// Edge is definitely not inside the legend
		if (((source.x < min.x) && (target.x < min.x)) || ((source.y < min.y) && (target.y < min.y)) || ((source.x > max.x) && (target.x > max.x))
			|| ((source.y > max.y) && (target.y > max.y))) {
			return false;
		}

		// Check every side of the legend for an intersection
		final float m = (float) (target.y - source.y) / (float) (target.x - source.x);
		float y = (m * (float) (min.x - source.x)) + (float) source.y;

		if ((y >= min.y) && (y <= max.y)) {
			return true;
		}

		y = (m * (float) (max.x - source.x)) + (float) source.y;
		if ((y >= min.y) && (y <= max.y)) {
			return true;
		}

		float x = ((float) (min.y - source.y) / m) + (float) source.x;
		if ((x >= min.x) && (x <= max.x)) {
			return true;
		}

		x = ((float) (max.y - source.y) / m) + (float) source.x;
		if ((x >= min.x) && (x <= max.x)) {
			return true;
		}

		return false;
	}

	/**
	 * Checks if the passed elements intersect any of the given rectangles and removes those rectangles from the list that happen to intersect something.
	 *
	 * Should it happen that the passed elements are features, their connections will be checked for an intersection as well.
	 *
	 * @param elements
	 * @param rects
	 * @param verticalLayout
	 */
	public void checkIntersections(List<? extends IGraphicalElement> elements, List<Rectangle> rects, boolean verticalLayout) {
		final ListIterator<Rectangle> iter = rects.listIterator();
		while (iter.hasNext()) {
			final Rectangle rect = iter.next();

			for (final IGraphicalElement element : elements) {
				final Rectangle elementRect = new Rectangle(FeatureUIHelper.getBounds(element));
				if (elementRect.intersects(rect)) {
					iter.remove();
					break;
				}

				if (element instanceof IGraphicalFeature) {
					final List<FeatureConnection> targets = ((IGraphicalFeature) element).getTargetConnections();
					if (checkConnectionIntersections(targets, rect, verticalLayout)) {
						iter.remove();
						break;
					}
				}
			}
		}
	}

	/**
	 * Checks for a certain feature if its connections are intersecting the given rectangle
	 *
	 * @param targets
	 * @param rect
	 * @param verticalLayout
	 * @return
	 */
	public boolean checkConnectionIntersections(List<FeatureConnection> targets, Rectangle rect, boolean verticalLayout) {
		for (int i = 0; i < targets.size(); i++) {
			Point target = null;
			Point source = null;
			if (!verticalLayout) {
				target = new Point(targets.get(i).getSource().getLocation().x + (targets.get(i).getSource().getSize().width / 2),
						targets.get(i).getSource().getLocation().y);
				source = new Point(targets.get(i).getTarget().getLocation().x + (targets.get(i).getTarget().getSize().width / 2),
						targets.get(i).getTarget().getLocation().y + targets.get(i).getTarget().getSize().height);
			} else {
				target = new Point(targets.get(i).getSource().getLocation().x,
						targets.get(i).getSource().getLocation().y + (targets.get(i).getSource().getSize().height / 2));
				source = new Point(targets.get(i).getTarget().getLocation().x + targets.get(i).getTarget().getSize().width,
						targets.get(i).getTarget().getLocation().y + (targets.get(i).getTarget().getSize().height / 2));
			}
			if (rectangleConnectionIntersection(source, target, rect)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Manages the placement of the legend
	 *
	 * @param featureModel
	 * @return new location of the legend
	 */
	public Point layoutLegend(IGraphicalFeatureModel featureModel) {
		if (!featureModel.getLayout().hasLegendAutoLayout()) {
			return null;
		}

		final Rectangle featureModelBounds = getFeatureModelBounds(featureModel.getVisibleFeatures());
		final Point min = featureModelBounds.getTopLeft();
		final Point max = featureModelBounds.getBottomRight();

		if (editor == null) {
			return null;
		}

		Dimension legendSize = null;
		LegendFigure legendFigure = null;
		for (final Object obj : editor.getEditPartRegistry().values()) {
			if (obj instanceof LegendEditPart) {
				legendFigure = ((LegendEditPart) obj).getFigure();
				legendSize = legendFigure.getSize();
			}
		}

		if ((legendSize == null) && (legendFigure == null)) {
			return null;
		}

		// Define positions for the legend that should be checked for an empty spot
		final ArrayList<Rectangle> rects = new ArrayList<Rectangle>();
		rects.add(new Rectangle(new Point(max.x - legendSize.width, min.y), legendSize));
		rects.add(new Rectangle(min, legendSize));
		rects.add(new Rectangle(new Point(min.x, max.y - legendSize.height()), legendSize));
		rects.add(new Rectangle(new Point(max.x - legendSize.width(), max.y - legendSize.height()), legendSize));

		// Check the first four positions for intersections with the features
		checkIntersections(featureModel.getVisibleFeatures(), rects, featureModel.getLayout().verticalLayout());

		// Add the position next to the featureModel and check for hits with the constraints
		rects.add(new Rectangle(new Point(max.x + FMPropertyManager.getFeatureSpaceX(), min.y), legendSize));
		checkIntersections(featureModel.getVisibleConstraints(), rects, featureModel.getLayout().verticalLayout());

		if (rects.size() > 0) {
			// At this point, rects does only contain positions for the legend that are acceptable. So we take the first
			featureModel.getLayout().setLegendPos(rects.get(0).getLocation().x, rects.get(0).getLocation().y);
			return featureModel.getLayout().getLegendPos();
		}

		// It was not possible to find any empty space, probably there is an intersection with a constraint.
		// So we position the legend next to the feature model and mind the constraints
		final Rectangle boundsOfEverything = getFeatureModelBounds(featureModel.getVisibleConstraints());
		boundsOfEverything.union(featureModelBounds);

		featureModel.getLayout().setLegendPos(boundsOfEverything.getTopRight().x + FMPropertyManager.getFeatureSpaceX(), min.y);
		return featureModel.getLayout().getLegendPos();
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
		if ((getLocation(feature) == null) || (feature.getSize() == null)) {
			// UIHelper not set up correctly, refresh the feature model
			feature.getObject().getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(getLocation(feature), feature.getSize());
	}

	protected List<IGraphicalFeature> getChildren(IGraphicalFeature feature) {
		return Functional.toList(feature.getGraphicalChildren(showHidden));
	}
}
