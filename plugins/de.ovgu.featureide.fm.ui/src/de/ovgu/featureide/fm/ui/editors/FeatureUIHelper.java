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

import java.beans.PropertyChangeEvent;
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

import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.FeatureConnection;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
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

	private static final WeakHashMap<IFeature, Point> featureLocation = new WeakHashMap<>();
	private static final WeakHashMap<IFeature, Dimension> featureSize = new WeakHashMap<>();
	private static final WeakHashMap<IConstraint, Point> constraintLocation = new WeakHashMap<>();
	private static final WeakHashMap<IConstraint, Dimension> constraintSize = new WeakHashMap<>();
	private static final WeakHashMap<IFeatureModel, Dimension> legendSize = new WeakHashMap<>();
	private static final WeakHashMap<IFeatureModel, LegendFigure> legendFigure = new WeakHashMap<>();

	/**
	 * Necessary for correct manual drag-and-drop movement while zoomed.
	 */
	private static double zoomFactor = 1.0;
	private static ZoomManager zoomManager = null;

	public static Dimension getLegendSize(IFeatureModel featureModel) {
		return legendSize.get(featureModel);
	}

	public static boolean showHiddenFeatures(IFeatureModel featureModel) {
		return featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures();
	}

	public static void showHiddenFeatures(boolean show, IFeatureModel featureModel) {
		featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures(show);
	}

	public static void setLegendSize(IFeatureModel featureModel, Dimension dim) {
		legendSize.put(featureModel, dim);
	}

	public static Point getLocation(IFeature feature) {
		return featureLocation.get(feature);
	}

	public static void setLocation(IFeature feature, FMPoint newLocation) {
		setLocation(feature, toPoint(newLocation));
	}

	public static void setLocation(IFeature feature, Point newLocation) {
		Point oldLocation = getLocation(feature);
		feature.getGraphicRepresenation().setNewLocation(toFMPoint(newLocation));
		if (newLocation == null) {
			return;
		}
		featureLocation.put(feature, newLocation);
		fireLocationChanged(feature, oldLocation, newLocation);
	}

	public static void setTemporaryLocation(IFeature feature, Point newLocation) {
		Point oldLocation = getLocation(feature);
		if (newLocation == null || newLocation.equals(oldLocation)) {
			return;
		}
		featureLocation.put(feature, newLocation);
		fireLocationChanged(feature, oldLocation, newLocation);
	}

	public static Dimension getSize(IFeature feature) {
		return featureSize.get(feature);
	}

	public static void setSize(IFeature feature, Dimension size) {
		featureSize.put(feature, size);
	}

	public static Rectangle getBounds(IFeature feature) {
		if (getLocation(feature) == null || getSize(feature) == null) {
			// UIHelper not set up correctly, refresh the feature model
			feature.getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(getLocation(feature), getSize(feature));
	}

	public static Rectangle getBounds(IConstraint constraint) {
		if (getLocation(constraint) == null || getSize(constraint) == null) {
			// UIHelper not set up correctly, refresh the feature model
			constraint.getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(getLocation(constraint), getSize(constraint));
	}

	public static List<ConnectionEditPart> getConnections(IFeature feature, EditPartViewer viewer) {
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

	private static void fireLocationChanged(IFeature feature, Point oldLocation, Point newLocation) {
		PropertyChangeEvent event = new PropertyChangeEvent(feature, PropertyConstants.LOCATION_CHANGED, oldLocation, newLocation);
		feature.fireEvent(event);
	}

	public static Point getReferencePoint(IFeature feature) {
		return getBounds(feature).getCenter();
	}

	public static Point calculateReferencePoint(IFeature feature, Point newLocation) {
		return new Rectangle(newLocation, getSize(feature)).getCenter();
	}

	public static Point getSourceLocation(IFeature feature) {
		IFeature parentFeature = feature;
		boolean parentFeatureHidden = false;
		while (!parentFeature.getStructure().isRoot()) {
			parentFeature = parentFeature.getStructure().getParent().getFeature();
			if (parentFeature.getStructure().isHidden()) {
				parentFeatureHidden = true;
			}
		}
		if ((feature.getStructure().isHidden() || parentFeatureHidden) && !feature.getFeatureModel().getGraphicRepresenation().getLayout().showHiddenFeatures()) {
			return getTargetLocation(feature.getStructure().getParent().getFeature());
		}

		return getSourceLocation(getBounds(feature), feature.getFeatureModel());
	}

	public static Point getSourceLocation(IFeature feature, Point newLocation) {
		return getSourceLocation(new Rectangle(newLocation, getSize(feature)), feature.getFeatureModel());
	}

	private static Point getSourceLocation(Rectangle bounds, IFeatureModel featureModel) {
		if (featureModel.getGraphicRepresenation().getLayout().verticalLayout()) {
			return new Point(bounds.getLeft().x, (bounds.bottom() + bounds.getTop().y) / 2);
		} else {
			return new Point(bounds.getCenter().x, bounds.y);
		}
	}

	public static Point getTargetLocation(IFeature feature) {
		Rectangle bounds = getBounds(feature);
		if (feature.getFeatureModel().getGraphicRepresenation().getLayout().verticalLayout()) {
			return new Point(bounds.getRight().x, (bounds.bottom() + bounds.getTop().y) / 2);
		}

		return new Point(bounds.getCenter().x, bounds.bottom() - 1);

	}

	public static void setVerticalLayoutBounds(boolean isVerticalLayout, IFeatureModel featureModel) {
		featureModel.getGraphicRepresenation().getLayout().verticalLayout(isVerticalLayout);
	}

	public static boolean hasVerticalLayout(IFeatureModel featureModel) {
		return featureModel.getGraphicRepresenation().getLayout().verticalLayout();
	}

	public static Dimension getSize(IConstraint constraint) {
		return constraintSize.get(constraint);
	}

	public static void setSize(IConstraint constraint, Dimension size) {
		constraintSize.put(constraint, size);
	}

	public static Point getLocation(IConstraint constraint) {
		return constraintLocation.get(constraint);
	}

	public static void setLocation(IConstraint constraint, FMPoint newLocation) {
		setLocation(constraint, toPoint(newLocation));
	}

	public static void setLocation(IConstraint constraint, Point newLocation) {
		Point oldLocation = getLocation(constraint);
		if (newLocation == null || newLocation.equals(oldLocation)) {
			return;
		}
		constraintLocation.put(constraint, newLocation);
		fireLocationChanged(constraint, oldLocation, newLocation);
		constraint.getGraphicRepresenation().setLocation(toFMPoint(newLocation));
	}

	private static void fireLocationChanged(IConstraint constraint, Point oldLocation, Point newLocation) {
		PropertyChangeEvent event = new PropertyChangeEvent(constraint, PropertyConstants.LOCATION_CHANGED, oldLocation, newLocation);
		constraint.fireEvent(event);
	}

	public static void setLegendFigure(IFeatureModel featureModel, LegendFigure figure) {
		legendFigure.put(featureModel, figure);
	}

	public static LegendFigure getLegendFigure(IFeatureModel featureModel) {
		return legendFigure.get(featureModel);
	}

	public static Point toPoint(FMPoint point) {
		return new Point(point.getX(), point.getY());
	}

	public static FMPoint toFMPoint(Point point) {
		return new FMPoint(point.x, point.y);
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
}
