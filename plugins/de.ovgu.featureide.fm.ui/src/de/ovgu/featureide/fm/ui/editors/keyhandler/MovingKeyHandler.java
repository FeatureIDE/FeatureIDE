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
package de.ovgu.featureide.fm.ui.editors.keyhandler;

import java.util.List;
import java.util.Map;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerKeyHandler;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;

import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureModelLayout;

/**
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class MovingKeyHandler extends GraphicalViewerKeyHandler {

	private enum Direction {
		LEFT, RIGHT
	};

	public MovingKeyHandler(GraphicalViewer viewer) {
		super(viewer);
	}

	@Override
	public boolean keyPressed(KeyEvent event) {
		// calls the super method if no arrow key was pressed
		if ((event.keyCode != SWT.ARROW_DOWN) && (event.keyCode != SWT.ARROW_LEFT) && (event.keyCode != SWT.ARROW_RIGHT) && (event.keyCode != SWT.ARROW_UP)) {
			return super.keyPressed(event);
		}

		final EditPart part = getViewer().getFocusEditPart();
		final Map<?, ?> editPartRegistry = getViewer().getEditPartRegistry();

		// true if a feature is selected
		if (part instanceof FeatureEditPart) {
			final FeatureEditPart featurepart = (FeatureEditPart) part;
			final IGraphicalFeature feature = featurepart.getModel();
			final IGraphicalFeature parent = feature.getSourceConnection().getTarget();
			final int dex = parent != null ? parent.getObject().getStructure().getChildIndex(feature.getObject().getStructure()) : 0;

			final FeatureModelLayout layout = feature.getGraphicalModel().getLayout();

			// checks if root bottom layout is chosen
			if (layout.getTopDownInverted()) {
				handleTopDownInvertedLayout(event, editPartRegistry, feature, parent, dex);
				return true;
			}

			// checks if root right layout is chosen
			if (layout.getLeftRightInverted()) {
				handleLeftRightInvertedLayout(event, editPartRegistry, feature, parent, dex);
				return true;
			}

			// checks if a top-down layout is chosen
			if (!feature.getGraphicalModel().getLayout().hasVerticalLayout()) {
				handleTopDownLayout(event, editPartRegistry, feature, parent, dex);
				return true;
				// in case that the left to right layout is chosen
			} else {
				handleLeftRightLayout(event, editPartRegistry, feature, parent, dex);
				return true;
			}

			// true if a constraint is selected
		} else if (part instanceof ConstraintEditPart) {
			final ConstraintEditPart constraint = (ConstraintEditPart) part;
			final List<IGraphicalConstraint> graphList = constraint.getModel().getGraphicalModel().getVisibleConstraints();
			final int dex = graphList.indexOf(constraint.getModel());
			if (event.keyCode == SWT.ARROW_UP) {
				if (dex > 0) {
					final Object o = editPartRegistry.get(graphList.get(dex - 1));
					navigateTo((EditPart) o, event);
				}
				return true;
			}
			if (event.keyCode == SWT.ARROW_DOWN) {
				if (dex < (graphList.size() - 1)) {
					final Object o = editPartRegistry.get(graphList.get(dex + 1));
					navigateTo((EditPart) o, event);
				}
				return true;
			}
			// ignore the left and right arrow key
			if ((event.keyCode == SWT.ARROW_LEFT) || (event.keyCode == SWT.ARROW_RIGHT)) {
				return true;
			}
		}
		return true;
	}

	private void handleLeftRightLayout(KeyEvent event, final Map<?, ?> editPartRegistry, final IGraphicalFeature feature, final IGraphicalFeature parent,
			final int dex) {
		// checks if the right arrow key is pressed and if the selected feature has visible children
		if ((event.keyCode == SWT.ARROW_RIGHT) && (feature.getGraphicalChildren() != null) && !feature.getGraphicalChildren().isEmpty()) {
			navigateTo((EditPart) editPartRegistry.get(feature.getGraphicalChildren().get(feature.getGraphicalChildren().size() / 2)), event);
		}
		// checks if the selected feature is the root
		if (parent != null) {
			if ((event.keyCode == SWT.ARROW_LEFT)) {
				navigateTo((EditPart) editPartRegistry.get(parent), event);
			}
			if ((event.keyCode == SWT.ARROW_DOWN)) {
				navigateTo(findNextFeature(feature, dex, Direction.RIGHT), event);
			}
			if ((event.keyCode == SWT.ARROW_UP)) {
				navigateTo(findNextFeature(feature, dex, Direction.LEFT), event);
			}
		}
	}

	private void handleLeftRightInvertedLayout(KeyEvent event, final Map<?, ?> editPartRegistry, final IGraphicalFeature feature,
			final IGraphicalFeature parent, final int dex) {
		// checks if the right arrow key is pressed and if the selected feature has visible children
		if ((event.keyCode == SWT.ARROW_LEFT) && (feature.getGraphicalChildren() != null) && !feature.getGraphicalChildren().isEmpty()) {
			navigateTo((EditPart) editPartRegistry.get(feature.getGraphicalChildren().get(feature.getGraphicalChildren().size() / 2)), event);
		}
		// checks if the selected feature is the root
		if (parent != null) {
			if ((event.keyCode == SWT.ARROW_RIGHT)) {
				navigateTo((EditPart) editPartRegistry.get(parent), event);
			}
			if ((event.keyCode == SWT.ARROW_DOWN)) {
				navigateTo(findNextFeature(feature, dex, Direction.RIGHT), event);
			}
			if ((event.keyCode == SWT.ARROW_UP)) {
				navigateTo(findNextFeature(feature, dex, Direction.LEFT), event);
			}
		}
	}

	private void handleTopDownLayout(KeyEvent event, final Map<?, ?> editPartRegistry, final IGraphicalFeature feature, final IGraphicalFeature parent,
			final int dex) {
		// checks if the down arrow key is pressed and if the selected feature has visible children
		if ((event.keyCode == SWT.ARROW_DOWN) && (feature.getGraphicalChildren() != null) && !feature.getGraphicalChildren().isEmpty()) {
			navigateTo((EditPart) editPartRegistry.get(feature.getGraphicalChildren().get(feature.getGraphicalChildren().size() / 2)), event);
			return;
		}
		// checks if the selected feature is the root
		if (parent != null) {
			if ((event.keyCode == SWT.ARROW_RIGHT)) {
				navigateTo(findNextFeature(feature, dex, Direction.RIGHT), event);
				return;
			}
			if ((event.keyCode == SWT.ARROW_LEFT)) {
				navigateTo(findNextFeature(feature, dex, Direction.LEFT), event);
				return;
			}
			if ((event.keyCode == SWT.ARROW_UP)) {
				navigateTo((EditPart) editPartRegistry.get(parent), event);
				return;
			}
		}
	}

	private void handleTopDownInvertedLayout(KeyEvent event, final Map<?, ?> editPartRegistry, final IGraphicalFeature feature, final IGraphicalFeature parent,
			final int dex) {
		// checks if the down arrow key is pressed and if the selected feature has visible children
		if ((event.keyCode == SWT.ARROW_UP) && (feature.getGraphicalChildren() != null) && !feature.getGraphicalChildren().isEmpty()) {
			navigateTo((EditPart) editPartRegistry.get(feature.getGraphicalChildren().get(feature.getGraphicalChildren().size() / 2)), event);
			return;
		}
		// checks if the selected feature is the root
		if (parent != null) {
			if ((event.keyCode == SWT.ARROW_RIGHT)) {
				navigateTo(findNextFeature(feature, dex, Direction.RIGHT), event);
				return;
			}
			if ((event.keyCode == SWT.ARROW_LEFT)) {
				navigateTo(findNextFeature(feature, dex, Direction.LEFT), event);
				return;
			}
			if ((event.keyCode == SWT.ARROW_DOWN)) {
				navigateTo((EditPart) editPartRegistry.get(parent), event);
				return;
			}
		}
	}

	private FeatureEditPart findNextFeature(IGraphicalFeature feature, int dex, Direction direct) {
		final IGraphicalFeature parent = feature.getSourceConnection().getTarget();
		final List<IGraphicalFeature> graphSiblings = parent.getGraphicalChildren();
		final Map<?, ?> editPartRegistry = getViewer().getEditPartRegistry();
		final boolean oneMore = checkForOneMore(graphSiblings, dex, direct);
		final int newDirection = (direct == Direction.RIGHT) ? 1 : (direct == Direction.LEFT) ? -1 : 0;
		// checks if there is an adjacent feature which has the same parent
		if (oneMore) {
			final IGraphicalFeature nextSibling = graphSiblings.get(dex + newDirection);
			final FeatureEditPart editPart = (FeatureEditPart) editPartRegistry.get(nextSibling);
			return editPart;
			// looks if there is an adjacent feature on the current layer
		} else {
			final IGraphicalFeature goalFeature = searchUp(feature, 0, direct);
			return (FeatureEditPart) editPartRegistry.get(goalFeature);
		}

	}

	private IGraphicalFeature searchUp(IGraphicalFeature feature, int layer, Direction direct) {
		final IGraphicalFeature parent = feature.getSourceConnection().getTarget();
		final List<IGraphicalFeature> siblings = parent.getGraphicalChildren();
		final int dex = siblings.indexOf(feature);
		final int listDirection = direct == Direction.LEFT ? -1 : 1;
		for (int i = dex + listDirection; (i < siblings.size()) && (i >= 0); i += listDirection) {
			final IGraphicalFeature ret = searchDown(siblings.get(i), layer, direct);
			if (ret != null) {
				return ret;
			}
		}
		if (parent.getObject().getStructure().isRoot()) {
			return null;
		}
		return searchUp(parent, layer + 1, direct);
	}

	private IGraphicalFeature searchDown(IGraphicalFeature feature, int layer, Direction direct) {
		if (layer == 0) {
			return feature;
		}
		final List<IGraphicalFeature> children = feature.getGraphicalChildren();
		if ((children != null) && !children.isEmpty()) {
			final int listDirection = direct == Direction.LEFT ? -1 : 1;
			final int listStart = direct == Direction.LEFT ? children.size() - 1 : 0;
			for (int i = listStart; (i < children.size()) && (i >= 0); i += listDirection) {
				final IGraphicalFeature ret = searchDown(children.get(i), layer - 1, direct);
				if (ret != null) {
					return ret;
				}
			}
		}
		return null;
	}

	/**
	 * looks if in the given direction is at least one more feature
	 */
	private boolean checkForOneMore(List<IGraphicalFeature> siblings, int dex, Direction direct) {
		if (direct == Direction.RIGHT) {
			return (dex < (siblings.size() - 1));
		} else if (direct == Direction.LEFT) {
			return dex > 0;
		}
		return false;
	}

}
