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
package de.ovgu.featureide.fm.ui.editors;

import java.util.Iterator;
import java.util.Map;

import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.DefaultEditDomain;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.ControlListener;
import org.eclipse.swt.events.FocusEvent;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.ChillScrollFreeformRootEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConnectionEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import de.ovgu.featureide.fm.ui.editors.keyhandler.FeatureDiagramEditorKeyHandler;
import de.ovgu.featureide.fm.ui.editors.mousehandler.FeatureDiagramEditorMouseHandler;
import de.ovgu.featureide.fm.ui.utils.ISearchable;
import de.ovgu.featureide.fm.ui.views.constraintview.ConstraintViewController;
import de.ovgu.featureide.fm.ui.views.constraintview.util.ConstraintViewDialog;

/**
 * An editor based on the Graphical Editing Framework to view and edit feature diagrams and cross-tree constraints.
 *
 * @author Thomas Thuem
 */
public class FeatureDiagramViewer extends ScrollingGraphicalViewer implements ISearchable<IGraphicalFeature>, GUIDefaults {

	public final class DiagramControlListener implements ControlListener {

		@Override
		public void controlResized(ControlEvent e) {
			/*
			 * Checks for null are necessary, because we cannot prevent this method being called before the model is loaded correctly (including positions in
			 * FeatureUIHelper). if (fm == null) return;
			 */

			final IGraphicalFeature object = FeatureUIHelper.getGraphicalRootFeature(graphicalFeatureModel);
			if (object == null) {
				return;
			}
			final org.eclipse.draw2d.geometry.Point oldLoc = object.getLocation();
			if (oldLoc == null) {
				return;
			}
			internRefresh(true);

			final org.eclipse.draw2d.geometry.Point newLoc = object.getLocation();
			if (newLoc == null) {
				return;
			}
			final int difX = newLoc.x - oldLoc.x;

			moveLegend(graphicalFeatureModel, difX);

			setLayout();
		}

		/**
		 * Moves the legend for the editor associated with feature model fm horizontally (used to move the legend along with the model when resizing the window)
		 *
		 * @param fm
		 * @param delta
		 */
		private void moveLegend(IGraphicalFeatureModel fm, int delta) {
			if (!graphicalFeatureModel.isLegendHidden()) {
				for (final Object obj : getEditPartRegistry().values()) {
					if (obj instanceof LegendEditPart) {
						final LegendFigure fig = ((LegendEditPart) obj).getFigure();
						fig.recreateLegend();
					}
				}
			}
		}

		@Override
		public void controlMoved(ControlEvent e) {
			// do nothing
		}
	}

	private ZoomManager zoomManager;

	private final IGraphicalFeatureModel graphicalFeatureModel;

	private final FeatureDiagramEditorKeyHandler editorKeyHandler;
	private FeatureDiagramLayoutManager layoutManager;

	private boolean openConstraintViewDecisionDialogAlreadySpawned = false;

	/**
	 * Constructor. Handles editable and read-only feature models.
	 *
	 * @param graphicalFeatureModel the graphical feature model
	 * @param editorPart the containing editorPart, if editable or {@code null}, if read-only
	 */
	public FeatureDiagramViewer(IGraphicalFeatureModel graphicalFeatureModel, IEditorPart editorPart) {
		super();
		this.graphicalFeatureModel = graphicalFeatureModel;

		setEditPartFactory(new GraphicalEditPartFactory());
		final ChillScrollFreeformRootEditPart rootEditPart = new ChillScrollFreeformRootEditPart();
		((ConnectionLayer) rootEditPart.getLayer(LayerConstants.CONNECTION_LAYER)).setAntialias(SWT.ON);
		setRootEditPart(rootEditPart);

		setZoomManager(rootEditPart.getZoomManager());
		getZoomManager().setZoomLevels(new double[] { 0.05, 0.10, 0.25, 0.375, 0.50, 0.625, 0.75, 0.90, 1.00, 1.10, 1.25, 1.50, 2.00, 2.50, 3.00, 4.00 });
		FeatureUIHelper.setZoomManager(getZoomManager());

		editorKeyHandler = new FeatureDiagramEditorKeyHandler(this, graphicalFeatureModel);
		setKeyHandler(editorKeyHandler);

		if (editorPart != null) {
			setEditDomain(new DefaultEditDomain(editorPart));
		}
	}

	/**
	 * Opens a dialog and asks the user if they want to show the constraint view.
	 */
	public void openConstraintDecision() {
		final IWorkbenchWindow bench = PlatformUI.getWorkbench().getActiveWorkbenchWindow();

		if (bench.getActivePage().findView(ConstraintViewController.ID) == null) {

			Display.getCurrent().asyncExec(new Runnable() {

				@Override
				public void run() {
					final boolean showConstraintView = ConstraintViewDialog.spawn();

					if (showConstraintView) {
						try {
							bench.getActivePage().showView(ConstraintViewController.ID);
						} catch (final PartInitException e) {
							e.printStackTrace();
						}
					}
				}
			});

		}
	}

	public FeatureDiagramViewer(IGraphicalFeatureModel graphicalFeatureModel) {
		this(graphicalFeatureModel, null);
	}

	/**
	 * Checks if the combined width including the spaces between features fits the editor's size. Based on the selected layout algorithm.
	 *
	 * @return true if the level fits in the editor.
	 */
	public boolean isLevelSizeOverLimit() {
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(graphicalFeatureModel);
		final double editorWidth = getFigureCanvas().getViewport().getSize().width / getZoomManager().getZoom();
		final double editorHeight = getFigureCanvas().getViewport().getSize().height / getZoomManager().getZoom();

		final double rootMidX = root.getLocation().x + (root.getSize().width / 2);
		final double rootMidY = root.getLocation().y - 10;

		final double borderLeft = rootMidX - (editorWidth / 2);
		final double borderRight = rootMidX + (editorWidth / 2);

		for (final IGraphicalFeature f : graphicalFeatureModel.getVisibleFeatures()) {
			if (f.getObject().getStructure().isRoot()) {
				continue;
			}
			if (((f.getLocation().x + f.getSize().width) > borderRight) || (f.getLocation().x < borderLeft)) {
				getFigureCanvas().getViewport().setViewLocation(new org.eclipse.draw2d.geometry.Point((int) borderLeft, (int) rootMidY));
				return true;
			}
			if (((f.getLocation().y + f.getSize().height) > editorHeight) || (f.getLocation().y < 0)) {
				getFigureCanvas().getViewport().setViewLocation(new org.eclipse.draw2d.geometry.Point((int) borderLeft, (int) rootMidY));
				return true;
			}
		}
		return false;
	}

	public boolean isNodeOutOfSight(IGraphicalFeature feature) {
		final IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(graphicalFeatureModel);
		final double editorWidth = (getFigureCanvas().getViewport().getSize().width / getZoomManager().getZoom());
		final double editorHeight = (getFigureCanvas().getViewport().getSize().height / getZoomManager().getZoom());

		final double rootMidX = root.getLocation().x + (root.getSize().width / 2);
		final double rootMidY = root.getLocation().y - (root.getSize().height / 2);

		final double borderLeft = rootMidX - (editorWidth / 2);
		double borderRight = rootMidX + (editorWidth / 2);
		if (borderLeft < -rootMidY) {
			borderRight = editorWidth - rootMidX;

		}
		double height = editorHeight;

		if (((int) editorHeight / 4) == (int) rootMidY) {
			height = editorHeight + rootMidY;
		}

		final int Xright = feature.getLocation().x + (feature.getSize().width / 2);
		if ((Xright > borderRight) || (feature.getLocation().x < borderLeft)) {
			getFigureCanvas().getViewport().setViewLocation(new org.eclipse.draw2d.geometry.Point((int) borderLeft, (int) rootMidY));
			return true;
		}
		final int YTop = feature.getLocation().y + (feature.getSize().height / 2);
		if ((YTop > height) || (feature.getLocation().y < 0)) {
			getFigureCanvas().getViewport().setViewLocation(new org.eclipse.draw2d.geometry.Point((int) borderLeft, (int) rootMidY));
			return true;
		}

		return false;
	}

	public void internRefresh(boolean onlyLayout) {
		if (getContents() == null) {
			return;
		}

		// refresh size of all feature figures
		if (!onlyLayout) {
			getContents().refresh();
		}

		// layout all features if autoLayout is enabled
		setLayout();

		// refresh position of all feature figures
		if (!onlyLayout) {
			getContents().refresh();
		}
	}

	public void reload() {// TODO do not layout twice
		// internRefresh(true);
		final Map<?, ?> editPartRegistry = getEditPartRegistry();
		final AbstractGraphicalEditPart abstractGraphicalEditPart = (AbstractGraphicalEditPart) editPartRegistry.get(graphicalFeatureModel);
		abstractGraphicalEditPart.refresh();
		internRefresh(true);
	}

	public void setLayout() {
		layoutManager = FeatureDiagramLayoutHelper.getLayoutManager(graphicalFeatureModel.getLayout().getLayoutAlgorithm(), graphicalFeatureModel);

		if (getControl() != null) {
			final Point size = getControl().getSize();
			layoutManager.setControlSize(size.x, size.y);
		}

		layoutManager.layout(graphicalFeatureModel, this);

		if (!graphicalFeatureModel.isLegendHidden() && graphicalFeatureModel.getLayout().hasLegendAutoLayout()) {
			for (final Object obj : getEditPartRegistry().values()) {
				if (obj instanceof LegendEditPart) {
					final LegendFigure fig = ((LegendEditPart) obj).getFigure();
					fig.recreateLegend();
				}
			}
		}
	}

	public void layoutLegendOnIntersect() {
		for (final Object obj : getEditPartRegistry().values()) {
			if (obj instanceof LegendEditPart) {
				final LegendFigure fig = ((LegendEditPart) obj).getFigure();
				fig.recreateLegend();
				final org.eclipse.draw2d.geometry.Point newLegendPosition = layoutManager.layoutLegend(graphicalFeatureModel);
				if (newLegendPosition != null) {
					fig.setLocation(newLegendPosition);
				}
			}
		}
	}

	public void deregisterEditParts() {
		final Map<?, ?> registry = getEditPartRegistry();
		for (final IGraphicalFeature f : graphicalFeatureModel.getFeatures()) {
			registry.remove(f);
			registry.remove(f.getSourceConnection());
		}
		for (final IGraphicalConstraint f : graphicalFeatureModel.getConstraints()) {
			registry.remove(f);
		}
	}

	public void deregisterEditParts(IGraphicalFeature feature) {
		final Map<?, ?> registry = getEditPartRegistry();
		registry.remove(feature);
		registry.remove(feature.getSourceConnection());
	}

	public void deregisterEditParts(IGraphicalConstraint constraint) {
		final Map<?, ?> registry = getEditPartRegistry();
		registry.remove(constraint);
	}

	/**
	 * Scrolls to the given points and center the view
	 *
	 * @param feature centerFeature
	 */
	public void centerPointOnScreen(IFeature feature) {
		final IGraphicalFeature graphFeature = graphicalFeatureModel.getGraphicalFeature(feature);
		final Map<?, ?> registryCollapsed = getEditPartRegistry();
		final Object featureEditPart = registryCollapsed.get(graphFeature);
		if (featureEditPart instanceof FeatureEditPart) {
			final FeatureEditPart editPart = (FeatureEditPart) featureEditPart;

			final int x = editPart.getFigure().getBounds().x;
			final int y = editPart.getFigure().getBounds().y;
			final int offsetX = editPart.getFigure().getBounds().width / 2;
			final int offsetY = editPart.getFigure().getBounds().height / 2;
			final int xCenter =
				(int) (((getZoomManager().getZoom() * x) - (getFigureCanvas().getViewport().getSize().width / 2)) + (getZoomManager().getZoom() * offsetX));
			final int yCenter =
				(int) (((getZoomManager().getZoom() * y) - (getFigureCanvas().getViewport().getSize().height / 2)) + (getZoomManager().getZoom() * offsetY));
			getFigureCanvas().getViewport().setViewLocation(xCenter, yCenter);
		}
	}

	public void refreshChildAll(IFeature parent) {
		for (final IFeatureStructure f : parent.getStructure().getChildren()) {
			// Refresh children
			refreshChildAll(f.getFeature());
		}
		refreshFeature(parent);
	}

	void refreshFeature(IFeature feature) {
		final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
		final FeatureEditPart editPart = (FeatureEditPart) getEditPartRegistry().get(graphicalFeature);
		if (editPart == null) {
			return;
		}

		// Refresh Connection
		for (final FeatureConnection connection : graphicalFeature.getTargetConnections()) {
			final ConnectionEditPart connectionEditPart = (ConnectionEditPart) getEditPartRegistry().get(connection);
			if (connectionEditPart != null) {
				connectionEditPart.refresh();
			}
		}
		// Refresh Feature
		editPart.refresh();
	}

	/**
	 * Stops the analyzing job when the editor is closed.
	 */
	public void dispose() {
		graphicalFeatureModel.getFeatureModelManager().removeListener(editorKeyHandler);
	}

	public IGraphicalFeatureModel getGraphicalFeatureModel() {
		return graphicalFeatureModel;
	}

	@Override
	public boolean matches(IGraphicalFeature element, String searchString) {
		return element.getObject().getName().toLowerCase().matches(".*" + searchString.toLowerCase() + ".*");
	}

	@Override
	public Iterator<IGraphicalFeature> createIterator() {
		return graphicalFeatureModel.getAllFeatures().iterator();
	}

	@Override
	public void found(IGraphicalFeature searchResult) {
		if (searchResult != null) {
			final EditPart editPart = (EditPart) getEditPartRegistry().get(searchResult);
			if (editPart != null) {
				select(editPart);
				reveal(editPart);
			}
		}
	}

	public ControlListener createControlListener() {
		return new DiagramControlListener();
	}

	public ZoomManager getZoomManager() {
		return zoomManager;
	}

	public void setZoomManager(ZoomManager zoomManager) {
		this.zoomManager = zoomManager;
	}

	public void createMouseHandlers() {
		// add scroll handler via shift
		getFigureCanvas().addMouseWheelListener(new FeatureDiagramEditorMouseHandler(SWT.SHIFT, getFigureCanvas()));
		// add scroll handler via middle mouse button
		getFigureCanvas().addMouseListener(new FeatureDiagramEditorMouseHandler(getFigureCanvas()));
	}

	@Override
	protected void handleFocusGained(FocusEvent fe) {

		if (!openConstraintViewDecisionDialogAlreadySpawned) {
			openConstraintViewDecisionDialogAlreadySpawned = true;
			openConstraintDecision();
		}
	}
}
