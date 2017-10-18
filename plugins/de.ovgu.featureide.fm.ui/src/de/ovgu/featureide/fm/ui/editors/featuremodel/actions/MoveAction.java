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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.MOVING;

import java.util.HashMap;
import java.util.Iterator;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.LegendFigure;

/**
 * This is the MoveAction for the manual movement of objects in the FeatureModelDiagram
 *
 * @author Guenter Ulreich
 * @author Andy Koch
 * @author Marcus Pinnecke
 */
public class MoveAction extends Action {

	public static final int stepwidth = 2;
	public static final String ID = "de.ovgu.featureide.move";
	public static final int UP = 1;
	public static final int RIGHT = 2;
	public static final int DOWN = 4;
	public static final int LEFT = 8;
	// whole movement has been stopped (needed for undo redo purposes)
	public static final int STOP = 0;

	private final int dir;

	private final Point deltaPos = new Point(0, 0);
	private final boolean doStop;
	private boolean isLegendMoving;

	private final GraphicalViewerImpl viewer;
	private final IGraphicalFeatureModel featureModel;

	private final HashMap<Object, Point> endPositions = new HashMap<Object, Point>();

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			// action only active when manual layout and feature diagram elements are selected
			setEnabled(isValidSelection((IStructuredSelection) event.getSelection()) && isMovingAllowed());

			// TODO: insert check for selection changed (would also end
			// transaction for moving)
		}
	};

	/**
	 *
	 * @param viewer the object which for the MoveAction has been registered
	 * @param featureModel the according FeatureModel object
	 * @param graphicalViewer the according GraphicalViewerImpl
	 * @param direction
	 */
	public MoveAction(Object viewer, IGraphicalFeatureModel featureModel, Object graphicalViewer, int direction) {
		super(MOVING);
		setId(ID);
		if (viewer instanceof GraphicalViewerImpl) {
			this.viewer = (GraphicalViewerImpl) viewer;
			this.viewer.addSelectionChangedListener(listener);
		} else {
			this.viewer = null;
		}
		this.featureModel = featureModel;
		dir = direction;
		setEnabled(false);
		doStop = (dir == STOP);

		if (!doStop) {
			switch (dir) {
			case DOWN:
				deltaPos.setY(stepwidth);
				break;
			case UP:
				deltaPos.setY(-stepwidth);
				break;
			case LEFT:
				deltaPos.setX(-stepwidth);
				break;
			case RIGHT:
				deltaPos.setX(stepwidth);
				break;
			}
		}
		init();
	}

	private void init() {
		endPositions.clear();
		isLegendMoving = false;
	}

	@Override
	public void run() {
		if (doStop) {
			stop();
		} else {
			doMove(false);
		}
	}

	/**
	 * Executes the requested move operation. and add it for undo and redo
	 */
	private void doMove(boolean doStop) {
		if (viewer != null) {
			for (final Iterator<?> it = ((IStructuredSelection) viewer.getSelection()).iterator(); it.hasNext();) {
				moveFigure(it.next(), doStop);
			}
		}
	}

	/**
	 * Tries to move the given figure.
	 *
	 * @param element graphical element to be moved
	 * @param doStop states whether new position is final position
	 */
	private void moveFigure(Object element, boolean doStop) {
		if ((element instanceof FeatureEditPart) || (element instanceof IFeature)) {
			final IGraphicalFeature feature = element instanceof FeatureEditPart ? ((FeatureEditPart) element).getModel() : (IGraphicalFeature) element;
			final Point newPos = feature.getLocation().translate(deltaPos);

			if (doStop) {
				endPositions.put(element, newPos);
			}

			feature.setLocation(newPos);
		} else if ((element instanceof ConstraintEditPart) || (element instanceof IConstraint)) {
			final IGraphicalConstraint constraint =
				element instanceof ConstraintEditPart ? ((ConstraintEditPart) element).getModel() : (IGraphicalConstraint) element;
			final Point newPos = constraint.getLocation().translate(deltaPos);
			constraint.setLocation(newPos);
		} else if ((element instanceof LegendEditPart) || (element instanceof LegendFigure)) {
			LegendFigure legendFigure = null;
			if (element instanceof LegendEditPart) {
				legendFigure = ((LegendEditPart) element).getFigure();
			} else if (element instanceof LegendFigure) {
				legendFigure = (LegendFigure) element;
			}
			final Point newPos = legendFigure.getLocation().translate(deltaPos);
			legendFigure.setLocation(newPos);
			featureModel.getLayout().setLegendPos(newPos.x(), newPos.y());
			featureModel.getLayout().setLegendAutoLayout(false);
			featureModel.handleLegendLayoutChanged();
			isLegendMoving = true;
		}
	}

	private void stop() {
		doMove(true);
		if (!isLegendMoving && featureModel.getLayout().hasLegendAutoLayout()) {
			featureModel.getFeatureModel().handleModelDataChanged();
		}

		init();
	}

	/**
	 * check the rules (actually, if there is AutoLayout not active)
	 *
	 * @return true if rules are not infringed
	 */
	private boolean isMovingAllowed() {
		return !featureModel.getLayout().hasFeaturesAutoLayout();
	}

	/**
	 * check if the selection has not only one element who is a ModelEditPart
	 *
	 * @param selection the IStructuredSelection object who contains the selected controls
	 * @return true if condition is matched
	 */
	private boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (only ModelEditPart is selected)
		return !((selection.size() == 1) && (selection.getFirstElement() instanceof ModelEditPart));
	}
}
