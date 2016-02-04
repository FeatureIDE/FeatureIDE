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
package de.ovgu.featureide.fm.ui.editors;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.editparts.ZoomListener;
import org.eclipse.gef.editparts.ZoomManager;

import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * this is a hack to quickly associate features with dimension and size (which
 * is not available in the model). luckily these informations do not need to be
 * stored persistently.
 * 
 * @author Christian Kaestner
 */
public class FeatureUIHelper {

	private static final Map<IGraphicalFeatureModel, Dimension> legendSize = new WeakHashMap<>();
	private static final Map<IGraphicalFeatureModel, LegendFigure> legendFigure = new WeakHashMap<>();

	/**
	 * Necessary for correct manual drag-and-drop movement while zoomed.
	 */
	private static double zoomFactor = 1.0;
	private static ZoomManager zoomManager = null;

	private static Point getSourceLocation(Rectangle bounds, IGraphicalFeatureModel featureModel) {
		if (featureModel.getLayout().verticalLayout()) {
			return bounds.getLeft();
		} else {
			return bounds.getTop();
		}
	}

	/**
	 * @return the zoomFactor
	 */
	public static double getZoomFactor() {
		return zoomFactor;
	}

	/**
	 * @param zoomFactor
	 *            the zoomFactor to set
	 */
	public static void setZoomFactor(double zoomFactor) {
		FeatureUIHelper.zoomFactor = zoomFactor;
	}

	/**
	 * @param zoomManager
	 */
	public static void setZoomManager(ZoomManager zoomManager) {
		FeatureUIHelper.zoomManager = zoomManager;
		if (zoomManager == null) {
			return;
		}
		zoomManager.addZoomListener(new ZoomListener() {
			@Override
			public void zoomChanged(double newZoomFactor) {
				FeatureUIHelper.zoomFactor = newZoomFactor;
			}
		});
	}

	/**
	 * @return the zoomManager
	 */
	public static ZoomManager getZoomManager() {
		return zoomManager;
	}

	public static Dimension getLegendSize(IGraphicalFeatureModel featureModel) {
		return legendSize.get(featureModel);
	}

	public static boolean showHiddenFeatures(IGraphicalFeatureModel featureModel) {
		return featureModel.getLayout().showHiddenFeatures();
	}

	public static void showHiddenFeatures(boolean show, IGraphicalFeatureModel featureModel) {
		featureModel.getLayout().showHiddenFeatures(show);
	}

	public static void setLegendSize(IGraphicalFeatureModel featureModel, Dimension dim) {
		legendSize.put(featureModel, dim);
	}

	public static Point getLocation(IGraphicalFeature feature) {
		return feature.getLocation();
	}

	public static void setLocation(IGraphicalFeature feature, Point newLocation) {
		Point oldLocation = getLocation(feature);
		if (oldLocation.equals(newLocation)) {
			return;
		}
		feature.setLocation(newLocation);
		fireLocationChanged(feature, oldLocation, newLocation);
	}

	public static void setTemporaryLocation(IGraphicalFeature feature, Point newLocation) {
		Point oldLocation = getLocation(feature);
		if (newLocation == null || newLocation.equals(oldLocation)) {
			return;
		}
		fireLocationChanged(feature, oldLocation, newLocation);
	}

	public static Dimension getSize(IGraphicalFeature feature) {
		return feature.getSize();
	}

	public static void setSize(IGraphicalFeature feature, Dimension size) {
		feature.setSize(size);
	}

	public static Rectangle getBounds(IGraphicalFeature feature) {
		if (getLocation(feature) == null || getSize(feature) == null) {
			// UIHelper not set up correctly, refresh the feature model
			feature.getObject().getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(getLocation(feature), getSize(feature));
	}

	public static Rectangle getBounds(IGraphicalConstraint constraint) {
		if (getLocation(constraint) == null || getSize(constraint) == null) {
			// UIHelper not set up correctly, refresh the feature model
			constraint.getObject().getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(getLocation(constraint), getSize(constraint));
	}

	public static List<ConnectionEditPart> getConnections(IGraphicalFeature feature, EditPartViewer viewer) {
		final List<ConnectionEditPart> editPartList = new LinkedList<ConnectionEditPart>();
		final Map<?, ?> registry = viewer.getEditPartRegistry();
		for (FeatureConnection connection : feature.getTargetConnections()) {
			final Object connectionEditPart = registry.get(connection);
			if (connectionEditPart instanceof ConnectionEditPart) {
				editPartList.add((ConnectionEditPart) connectionEditPart);
			}
		}
		return editPartList;
	}

	public static Point getReferencePoint(IGraphicalFeature feature) {
		return getBounds(feature).getCenter();
	}

	public static Point calculateReferencePoint(IGraphicalFeature feature, Point newLocation) {
		return new Rectangle(newLocation, getSize(feature)).getCenter();
	}

	public static Point getSourceLocation(IGraphicalFeature feature) {
		IFeatureStructure parentFeature = feature.getObject().getStructure();
		boolean parentFeatureHidden = false;
		while (!parentFeature.isRoot()) {
			parentFeature = parentFeature.getParent();
			if (parentFeature.isHidden()) {
				parentFeatureHidden = true;
			}
		}
		if ((feature.getObject().getStructure().isHidden() || parentFeatureHidden)
				&& !feature.getGraphicalModel().getLayout().showHiddenFeatures()) {
			return getTargetLocation(feature.getTree().getParentObject());
		}

		return getSourceLocation(getBounds(feature), feature.getGraphicalModel());
	}

	public static Point getSourceLocation(IGraphicalFeature feature, Point newLocation) {
		return getSourceLocation(new Rectangle(newLocation, getSize(feature)), feature.getGraphicalModel());
	}

	public static Point getTargetLocation(IGraphicalFeature feature) {
		final Rectangle bounds = getBounds(feature);
		if (feature.getGraphicalModel().getLayout().verticalLayout()) {
			return bounds.getRight();
		}
		return bounds.getBottom();

	}

	public static void setVerticalLayoutBounds(boolean isVerticalLayout, IGraphicalFeatureModel featureModel) {
		featureModel.getLayout().verticalLayout(isVerticalLayout);
	}

	public static boolean hasVerticalLayout(IGraphicalFeatureModel featureModel) {
		return featureModel.getLayout().verticalLayout();
	}

	public static Dimension getSize(IGraphicalConstraint constraint) {
		return constraint.getSize();
	}

	public static void setSize(IGraphicalConstraint constraint, Dimension size) {
		constraint.setSize(size);
	}

	public static Point getLocation(IGraphicalConstraint constraint) {
		return constraint.getLocation();
	}

	public static void setLocation(IGraphicalConstraint constraint, Point newLocation) {
		Point oldLocation = getLocation(constraint);
		if (newLocation == null || newLocation.equals(oldLocation)) {
			return;
		}
		constraint.setLocation(newLocation);
		fireLocationChanged(constraint, oldLocation, newLocation);
	}

	private static void fireLocationChanged(IGraphicalFeature feature, Point oldLocation, Point newLocation) {
//		FeatureIDEEvent event = new FeatureIDEEvent(feature, EventType.LOCATION_CHANGED, oldLocation, newLocation);
//		feature.getObject().fireEvent(event);
	}
	
	private static void fireLocationChanged(IGraphicalConstraint constraint, Point oldLocation, Point newLocation) {
		FeatureIDEEvent event = new FeatureIDEEvent(constraint, EventType.LOCATION_CHANGED, oldLocation, newLocation);
		constraint.getObject().fireEvent(event);
	}

	public static void setLegendFigure(IGraphicalFeatureModel featureModel, LegendFigure figure) {
		legendFigure.put(featureModel, figure);
	}

	public static LegendFigure getLegendFigure(IGraphicalFeatureModel featureModel) {
		return legendFigure.get(featureModel);
	}

}
