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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
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
 */
abstract public class FeatureDiagramLayoutManager {

	protected int controlWidth = 10;
	protected int controlHeight = 10;
	protected boolean showHidden, showCollapsedConstraints;
	protected FeatureDiagramEditor editor;
	private boolean firstManualLayout = false;

	public final void layout(IGraphicalFeatureModel featureModel, FeatureDiagramEditor editor) {
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
				// start peform the location changed event to refresh the connection only in manual layout
				entry.update(FeatureIDEEvent.getDefault(EventType.LOCATION_CHANGED));
				firstManualLayout = true;
			}
		}

		if (!featureModel.isLegendHidden() && featureModel.getLayout().hasLegendAutoLayout()) {
			layoutLegend(featureModel, showHidden);
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
		int y = yoffset + FMPropertyManager.getConstraintSpace() * 2;
		boolean depthFirst = this instanceof DepthFirstLayout || this instanceof VerticalLayout;
		for (IGraphicalConstraint constraint : constraints) {
			final Dimension size = constraint.getSize();
			int x;
			if (depthFirst) {
				x = 2 * FMPropertyManager.getFeatureSpaceX();
			} else {
				final int rootCenter = rootBounds.x + (rootBounds.width / 2);
				x = rootCenter - (size.width / 2);
			}
			constraint.setLocation(new Point(x, y));

			y += size.height;
		}
	}

	/**
	 * sets the position of the legend
	 */
	public void layoutLegend(IGraphicalFeatureModel featureModel, boolean showHidden) {
		final Point min = new Point(Integer.MAX_VALUE, Integer.MAX_VALUE);
		final Point max = new Point(Integer.MIN_VALUE, Integer.MIN_VALUE);

		/*
		 * update lowest, highest, most left, most right coordinates for features
		 */
		final Iterable<IGraphicalFeature> nonHidden = featureModel.getVisibleFeatures();
		for (final IGraphicalFeature feature : nonHidden) {
			final Rectangle position = FeatureUIHelper.getBounds(feature);
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

		/*
		 * update lowest, highest, most left, most right coordinates for constraints
		 */
		for (final IGraphicalConstraint constraint : featureModel.getVisibleConstraints()) {
			final Rectangle position = FeatureUIHelper.getBounds(constraint);
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
		if (editor == null) {
			return;
		}
		Dimension legendSize = null;
		LegendFigure legendFigure = null;
		// Find Legend Figure
		for (final Object obj : editor.getEditPartRegistry().values()) {
			if (obj instanceof LegendEditPart) {
				legendFigure = ((LegendEditPart) obj).getFigure();
				legendSize = legendFigure.getSize();
			}
		}
		if ((legendSize == null) && (legendFigure == null)) {
			return;
		}

		boolean topRight = true;
		boolean topLeft = true;
		boolean botLeft = true;
		boolean botRight = true;

		/*
		 * check if features would intersect with the legend on the edges
		 */
		for (final IGraphicalFeature feature : nonHidden) {
			final Point tempLocation = feature.getLocation();
			if (null != tempLocation) {
				final Dimension tempSize = feature.getSize();
				if (tempSize != null) {
					if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						topRight = false;
					}
					if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						topLeft = false;
					}
					if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						botLeft = false;
					}
					if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						botRight = false;
					}
				}
			}
		}
		/*
		 * check if constraints would intersect with the legend on the edges
		 */
		if (topRight || topLeft || botLeft || botRight) {
			for (final IGraphicalConstraint constraint : featureModel.getVisibleConstraints()) {
				final Point tempLocation = constraint.getLocation();
				if (null == tempLocation) {
					continue;
				}
				final Dimension tempSize = constraint.getSize();
				if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
					&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
					topRight = false;
				}
				if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
					&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
					topLeft = false;
				}
				if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
					&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
					botLeft = false;
				}
				if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
					&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
					botRight = false;
				}
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
	 * sets the position of the legend only when intersecting
	 */
	public Point layoutLegendOnIntersect(IGraphicalFeatureModel featureModel) {
		final Point min = new Point(Integer.MAX_VALUE, Integer.MAX_VALUE);
		final Point max = new Point(Integer.MIN_VALUE, Integer.MIN_VALUE);

		/*
		 * update lowest, highest, most left, most right coordinates for features
		 */
		final Iterable<IGraphicalFeature> nonHidden = featureModel.getVisibleFeatures();
		for (final IGraphicalFeature feature : nonHidden) {
			final Rectangle position = FeatureUIHelper.getBounds(feature);
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

		/*
		 * update lowest, highest, most left, most right coordinates for constraints
		 */
		for (final IGraphicalConstraint constraint : featureModel.getVisibleConstraints()) {
			final Rectangle position = FeatureUIHelper.getBounds(constraint);
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
		if (editor == null) {
			return null;
		}
		Dimension legendSize = null;
		LegendFigure legendFigure = null;
		// Find Legend Figure
		for (final Object obj : editor.getEditPartRegistry().values()) {
			if (obj instanceof LegendEditPart) {
				legendFigure = ((LegendEditPart) obj).getFigure();
				legendSize = legendFigure.getSize();
			}
		}
		if ((legendSize == null) && (legendFigure == null)) {
			return null;
		}

		boolean topRight = true;
		boolean topLeft = true;
		boolean botLeft = true;
		boolean botRight = true;

		boolean intersects = false;

		final Rectangle legend = legendFigure.getBounds();

		for (final IGraphicalFeature feature : nonHidden) {
			final Point tempLocation = feature.getLocation();
			if (null != tempLocation) {
				final Rectangle featureRect = new Rectangle(tempLocation, feature.getSize());
				if (legend.intersects(featureRect)) {
					intersects = true;
				}
			}
		}
		for (final IGraphicalConstraint consts : featureModel.getVisibleConstraints()) {
			final Point tempLocation = consts.getLocation();
			if (null != tempLocation) {
				final Rectangle featureRect = new Rectangle(tempLocation, consts.getSize());
				if (legend.intersects(featureRect)) {
					intersects = true;
				}
			}
		}

		if (intersects) {
			/*
			 * check if features would intersect with the legend on the edges
			 */
			for (final IGraphicalFeature feature : nonHidden) {
				final Point tempLocation = feature.getLocation();
				if (null != tempLocation) {
					final Dimension tempSize = feature.getSize();
					if (tempSize != null) {
						if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
							&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
							topRight = false;
						}
						if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
							&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
							topLeft = false;
						}
						if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
							&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
							botLeft = false;
						}
						if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
							&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
							botRight = false;
						}
					}
				}
			}
			/*
			 * check if constraints would intersect with the legend on the edges
			 */
			if (topRight || topLeft || botLeft || botRight) {
				for (final IGraphicalConstraint constraint : featureModel.getVisibleConstraints()) {
					final Point tempLocation = constraint.getLocation();
					if (null == tempLocation) {
						continue;
					}
					final Dimension tempSize = constraint.getSize();
					if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						topRight = false;
					}
					if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y) < (min.y + legendSize.height + (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						topLeft = false;
					}
					if (((tempLocation.x) < (min.x + legendSize.width + FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						botLeft = false;
					}
					if (((tempLocation.x + tempSize.width) > (max.x - legendSize.width - FMPropertyManager.getFeatureSpaceX()))
						&& ((tempLocation.y + tempSize.height) > (max.y - legendSize.height - (FMPropertyManager.getFeatureSpaceY() / 2)))) {
						botRight = false;
					}
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
			return featureModel.getLayout().getLegendPos();
		} else {
			return null;
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
