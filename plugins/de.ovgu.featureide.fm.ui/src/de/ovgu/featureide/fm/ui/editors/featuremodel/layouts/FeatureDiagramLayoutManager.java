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

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.FeatureConnection;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
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
				// start perform the location changed event to refresh the connection only in manual layout
				entry.update(FeatureIDEEvent.getDefault(EventType.LOCATION_CHANGED));
				firstManualLayout = true;
			}
		}

		if (!featureModel.isLegendHidden()) {
			if (featureModel.getLayout().hasLegendAutoLayout()) {
				layoutLegend(featureModel, showHidden);
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

	void layout(int yoffset, List<IGraphicalConstraint> constraints) {
		// added 2 times getConstraintSpace to prevent intersecting with the collapsed decorator
		int y = yoffset + (FMPropertyManager.getConstraintSpace() * 2);
		final boolean depthFirst = (this instanceof DepthFirstLayout) || (this instanceof VerticalLayout);
		for (final IGraphicalConstraint constraint : constraints) {
			final Dimension size = constraint.getSize();
			final int x = depthFirst ? 2 * FMPropertyManager.getFeatureSpaceX() : (controlWidth - size.width) >> 1;
			constraint.setLocation(new Point(x, y));
			y += size.height;
		}
	}
	
	public Point[] getFeatureModelBounds(IGraphicalFeatureModel featureModel, boolean showHidden) {
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

		Point[] bounds = new Point[2];
		bounds[0] = new Point(min.x, min.y);
		bounds[1] = new Point(max.x, max.y);		
		return bounds;
	}
	
	public boolean checkConnectionIntersection(Point source, Point target, Point legendPos, Dimension legendSize) {
		int legendWidth = legendPos.x + legendSize.width;
		int legendHeight = legendPos.y + legendSize.height;
		
		//Edge is definitely not inside the legend
		if ((source.x < legendPos.x && target.x < legendPos.x) ||
		    (source.y < legendPos.y && target.y < legendPos.y) ||
		    (source.x > legendWidth && target.x > legendWidth) ||
		    (source.y > legendHeight && target.y > legendHeight))
			return false;
		
		//Check every side of the legend for an intersection
		float m = (float)(target.y - source.y) / (float)(target.x - source.x);
		float y = m * (float)(legendPos.x - source.x) + (float)source.y;
		
	    if (y >= legendPos.y && y <= legendHeight)
	    	return true;

	    y = m * (float)(legendWidth - source.x) + (float)source.y;
	    if (y >= legendPos.y && y <= legendHeight)
	    	return true;

	    float x = (float)(legendPos.y - source.y) / m + (float)source.x;
	    if (x >= legendPos.x && x <= legendWidth)
	    	return true;

	    x = (float)(legendHeight - source.y) / m + (float)source.x;
	    if (x >= legendPos.x && x <= legendWidth)
	    	return true;
	    
	    return false;
	}
	
	public void checkIntersections(List<? extends IGraphicalElement> elements, List<Rectangle> rects, boolean verticalLayout) {
		ListIterator<Rectangle> iter = rects.listIterator();
		while(iter.hasNext()) {
			Rectangle rect = iter.next();
			
			for (final IGraphicalElement element : elements) {
				Rectangle elementRect = new Rectangle(element.getLocation(), element.getSize());
				if (elementRect.intersects(rect)) {
					iter.remove();
					break;
				}
				
				if (element instanceof IGraphicalFeature) {
					List<FeatureConnection> targets = ((IGraphicalFeature) element).getTargetConnections();
					if (checkConnectionIntersections(targets, rect, verticalLayout)) {
						iter.remove();
						break;
					}
				}
			}
		}
	}
	
	public boolean checkConnectionIntersections(List<FeatureConnection> targets, Rectangle rect, boolean verticalLayout) {
		for (int i = 0; i < targets.size(); i++) {
			Point target = null;
			Point source = null;
			if (verticalLayout) {
				target = new Point(targets.get(i).getSource().getLocation().x + targets.get(i).getSource().getSize().width/2, 
					   targets.get(i).getSource().getLocation().y);
				source = new Point(targets.get(i).getTarget().getLocation().x + targets.get(i).getTarget().getSize().width/2, 
					   targets.get(i).getTarget().getLocation().y + targets.get(i).getTarget().getSize().height);
			} else {
				target = new Point(targets.get(i).getSource().getLocation().x, 
					   targets.get(i).getSource().getLocation().y + targets.get(i).getSource().getSize().height/2);
				source = new Point(targets.get(i).getTarget().getLocation().x + targets.get(i).getTarget().getSize().width, 
					   targets.get(i).getTarget().getLocation().y + targets.get(i).getTarget().getSize().height/2);
			}
			if (checkConnectionIntersection(source, target, rect.getLocation(), rect.getSize()))
				return true;
		}
		return false;
	}
	
	public Point layoutLegend(IGraphicalFeatureModel featureModel, boolean showHidden) {
		if (!featureModel.getLayout().hasLegendAutoLayout())
			return null;
		
		Point[] featureModelBounds = getFeatureModelBounds(featureModel, showHidden);
		final Point min = featureModelBounds[0];
		final Point max = featureModelBounds[1];
		if (editor == null)
			return null;

		Dimension legendSize = null;
		LegendFigure legendFigure = null;
		for (final Object obj : editor.getEditPartRegistry().values()) {
			if (obj instanceof LegendEditPart) {
				legendFigure = ((LegendEditPart) obj).getFigure();
				legendSize = legendFigure.getSize();
			}
		}
		
		if ((legendSize == null) && (legendFigure == null))
			return null;
		
		ArrayList<Rectangle> rects = new ArrayList<Rectangle>();
		rects.add(new Rectangle(new Point(max.x - legendSize.width, min.y), legendSize));
		rects.add(new Rectangle(min, legendSize));
		rects.add(new Rectangle(new Point(min.x, max.y - legendSize.height()), legendSize));
		rects.add(new Rectangle(new Point(max.x - legendSize.width(), max.y - legendSize.height()), legendSize));
		
		checkIntersections(featureModel.getVisibleFeatures(), rects, featureModel.getLayout().verticalLayout());
		checkIntersections(featureModel.getVisibleConstraints(), rects, featureModel.getLayout().verticalLayout());
		
		if(rects.size() > 0) {
			featureModel.getLayout().setLegendPos(rects.get(0).getLocation().x, rects.get(0).getLocation().y);
			return featureModel.getLayout().getLegendPos();
		}
		
		featureModel.getLayout().setLegendPos(max.x + FMPropertyManager.getFeatureSpaceX(), min.y);
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
