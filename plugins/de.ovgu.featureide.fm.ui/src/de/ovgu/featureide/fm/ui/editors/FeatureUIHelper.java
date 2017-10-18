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
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.editparts.ZoomListener;
import org.eclipse.gef.editparts.ZoomManager;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;

/**
 * this is a hack to quickly associate features with dimension and size (which is not available in the model). luckily these informations do not need to be
 * stored persistently.
 *
 * @author Christian Kaestner
 */
public class FeatureUIHelper {

	public static boolean isAncestorOf(IGraphicalFeature feature, IGraphicalFeature parent) {
		return FeatureUtils.isAncestorOf(feature.getObject(), parent.getObject());
	}

	public static IGraphicalFeature getGraphicalRootFeature(IGraphicalFeatureModel model) {
		return getGraphicalFeature(model.getFeatureModel().getStructure().getRoot(), model);
	}

	public static IGraphicalElement getGraphicalElement(IFeatureModelElement element, IGraphicalFeatureModel model) {
		if (element instanceof IConstraint) {
			return getGraphicalConstraint((IConstraint) element, model);
		} else {
			return getGraphicalFeature((IFeature) element, model);
		}
	}

	public static IGraphicalElement getGraphicalConstraint(IConstraint constraint, IGraphicalFeatureModel model) {
		return model.getGraphicalConstraint(constraint);
	}

	public static IGraphicalFeature getGraphicalFeature(IFeatureStructure feature, IGraphicalFeatureModel model) {
		return getGraphicalFeature(feature.getFeature(), model);
	}

	public static IGraphicalFeature getGraphicalFeature(IFeature feature, IGraphicalFeatureModel model) {
		return model.getGraphicalFeature(feature);
	}

	public static IGraphicalFeature getGraphicalParent(IGraphicalFeature feature) {
		return getGraphicalParent(feature.getObject(), feature.getGraphicalModel());
	}

	public static IGraphicalFeature getGraphicalParent(IFeature feature, IGraphicalFeatureModel model) {
		final IFeatureStructure structure = feature.getStructure();
		return structure.isRoot() ? null : getGraphicalFeature(structure.getParent(), model);
	}

	public static List<IGraphicalFeature> getGraphicalSiblings(final IGraphicalFeature feature) {
		final IFeatureStructure structure = feature.getObject().getStructure();
		if (structure.isRoot()) {
			return Arrays.asList(getGraphicalFeature(structure, feature.getGraphicalModel()));
		}
		return getGraphicalChildren(structure.getParent().getFeature(), feature.getGraphicalModel());
	}

	public static List<IGraphicalFeature> getGraphicalChildren(final IGraphicalFeature feature) {
		return getGraphicalChildren(feature.getObject(), feature.getGraphicalModel());
	}

	public static List<IGraphicalFeature> getGraphicalChildren(final IFeature feature, IGraphicalFeatureModel model) {
		final List<IFeatureStructure> children = feature.getStructure().getChildren();
		final List<IGraphicalFeature> graphicalChildren = new ArrayList<>(children.size());
		for (final IFeatureStructure child : children) {
			final IGraphicalFeature graphicChild = getGraphicalFeature(child, model);
			if (!graphicChild.hasCollapsedParent() && (!child.hasHiddenParent() || model.getLayout().showHiddenFeatures())) {
				graphicalChildren.add(graphicChild);
			}
		}
		return graphicalChildren;
	}

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
	 * @param zoomFactor the zoomFactor to set
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

	public static boolean showHiddenFeatures(IGraphicalFeatureModel featureModel) {
		return featureModel.getLayout().showHiddenFeatures();
	}

	public static void showHiddenFeatures(boolean show, IGraphicalFeatureModel featureModel) {
		featureModel.getLayout().showHiddenFeatures(show);
	}

	public static void showCollapsedConstraints(boolean show, IGraphicalFeatureModel featureModel) {
		featureModel.getLayout().showCollapsedConstraints(show);
	}

	public static Rectangle getBounds(IGraphicalFeature feature) {
		if ((feature.getLocation() == null) || (feature.getSize() == null)) {
			// UIHelper not set up correctly, refresh the feature model
			feature.getObject().getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(feature.getLocation(), feature.getSize());
	}

	public static Rectangle getBounds(IGraphicalConstraint constraint) {
		if ((constraint.getLocation() == null) || (constraint.getSize() == null)) {
			// UIHelper not set up correctly, refresh the feature model
			constraint.getObject().getFeatureModel().handleModelDataChanged();
		}
		return new Rectangle(constraint.getLocation(), constraint.getSize());
	}

	/**
	 * should not be used here
	 */
	@Deprecated
	public static List<ConnectionEditPart> getConnections(IGraphicalFeature feature, EditPartViewer viewer) {
		final List<ConnectionEditPart> editPartList = new LinkedList<ConnectionEditPart>();
		final Map<?, ?> registry = viewer.getEditPartRegistry();
		for (final FeatureConnection connection : feature.getTargetConnections()) {
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
		return new Rectangle(newLocation, feature.getSize()).getCenter();
	}

	public static Point getSourceLocation(IGraphicalFeature feature) {
		/*
		 * Checks if the feature is hidden or has a hidden parent and hidden features should not be shown or if the feature has a collapsed parent and should
		 * therefore not be shown.
		 */
		if ((feature.getObject().getStructure().hasHiddenParent() && !feature.getGraphicalModel().getLayout().showHiddenFeatures())
			|| feature.hasCollapsedParent()) {
			return getTargetLocation(getGraphicalParent(feature));
		}

		return getSourceLocation(getBounds(feature), feature.getGraphicalModel());
	}

	public static Point getSourceLocation(IGraphicalFeature feature, Point newLocation) {
		return getSourceLocation(new Rectangle(newLocation, feature.getSize()), feature.getGraphicalModel());
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

}
