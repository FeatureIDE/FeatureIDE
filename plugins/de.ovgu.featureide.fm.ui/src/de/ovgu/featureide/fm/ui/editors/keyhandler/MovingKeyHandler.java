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
package de.ovgu.featureide.fm.ui.editors.keyhandler;

import java.util.List;
import java.util.Map;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerKeyHandler;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * TODO description
 *
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class MovingKeyHandler extends GraphicalViewerKeyHandler {

	public enum direction {
		left, right
	};

	public MovingKeyHandler(GraphicalViewer viewer) {
		super(viewer);
	}

	@Override
	public boolean keyPressed(KeyEvent event) {
		final EditPart part = getViewer().getFocusEditPart();
		final Map<?, ?> editPartRegistry = getViewer().getEditPartRegistry();
		if (part instanceof FeatureEditPart) {
			final FeatureEditPart featurepart = (FeatureEditPart) part;
			final IGraphicalFeature feature = featurepart.getModel();
			final IGraphicalFeature parent = feature.getSourceConnection().getTarget();
			final int dex = parent != null ? parent.getObject().getStructure().getChildIndex(feature.getObject().getStructure()) : 0;
			if (!feature.getGraphicalModel().getLayout().verticalLayout()) {
				if ((event.keyCode == SWT.ARROW_DOWN) && (feature.getGraphicalChildren(false) != null) && !feature.getGraphicalChildren(false).isEmpty()) {
					navigateTo((EditPart) editPartRegistry.get(feature.getGraphicalChildren(false).get(0)), event);
					return true;
				}
				if (parent != null) {
					if ((event.keyCode == SWT.ARROW_RIGHT) && (parent != null)) {
						navigateTo(findNextFeature(feature, dex, 1, direction.right), event);
						return true;
					}
					if ((event.keyCode == SWT.ARROW_LEFT) && (parent != null)) {
						navigateTo(findNextFeature(feature, dex, 1, direction.left), event);
						return true;
					}
					if ((event.keyCode == SWT.ARROW_UP) && (parent != null)) {
						navigateTo((EditPart) editPartRegistry.get(parent), event);
						return true;
					}
				} else {
					return true;
				}

			} else {
				if ((event.keyCode == SWT.ARROW_RIGHT) && (feature.getGraphicalChildren(false) != null) && !feature.getGraphicalChildren(false).isEmpty()) {
					navigateTo((EditPart) editPartRegistry.get(feature.getGraphicalChildren(false).get(feature.getGraphicalChildren(false).size() / 2)), event);
					return true;
				}
				if (parent != null) {
					if ((event.keyCode == SWT.ARROW_LEFT)) {
						navigateTo((EditPart) editPartRegistry.get(parent), event);
						return true;
					}
					if ((event.keyCode == SWT.ARROW_DOWN)) {
						navigateTo(findNextFeature(feature, dex, 1, direction.right), event);
						return true;
					}
					if ((event.keyCode == SWT.ARROW_UP)) {
						navigateTo(findNextFeature(feature, dex, 1, direction.left), event);
						return true;
					}
				} else {
					return true;
				}
			}

		}
		return super.keyPressed(event);
	}

	/**
	 * navigates to next feature on the right, which is on the same layer as
	 *
	 * @param parent
	 * @param dex
	 * @param layer
	 */
	private FeatureEditPart findNextFeature(IGraphicalFeature feature, int dex, int layer, direction direct) {
		final IGraphicalFeature parent = feature.getSourceConnection().getTarget();
		final List<IFeatureStructure> siblings = parent.getObject().getStructure().getChildren();
		final Map<?, ?> editPartRegistry = getViewer().getEditPartRegistry();
		final boolean oneMore = checkForOneMore(siblings, dex, direct);
		final int newDirections = (direct == direction.right) ? 1 : (direct == direction.left) ? -1 : 0;
		if (oneMore && (layer == 1)) {
			final IFeature nextSibling = siblings.get(dex + newDirections).getFeature();
			final IGraphicalFeature nextGraphicalSibling = parent.getGraphicalModel().getGraphicalFeature(nextSibling);
			final FeatureEditPart editPart = (FeatureEditPart) editPartRegistry.get(nextGraphicalSibling);
			return editPart;
		} else if (oneMore && (layer != 1)) {
			for (int i = dex + newDirections; (i < siblings.size()) && (i >= 0); i = i + newDirections) {
				IFeatureStructure nextSibling = siblings.get(i);
				for (int l = 1; l < layer; l++) {
					final List<IFeatureStructure> descendants = nextSibling.getChildren();
					if ((descendants != null) && !descendants.isEmpty()) {
						final int neighbor = (direct == direction.right) ? 0 : descendants.size() - 1;
						nextSibling = descendants.get(neighbor);
						if (l == (layer - 1)) {
							final IGraphicalFeature ret = feature.getGraphicalModel().getGraphicalFeature(nextSibling.getFeature());
							return (FeatureEditPart) editPartRegistry.get(ret);

						}
					} else {
						break;
					}
				}
			}
			final IGraphicalFeature grandParent = parent.getSourceConnection().getTarget();
			final int newDex = grandParent.getObject().getStructure().getChildIndex(parent.getObject().getStructure());
			return findNextFeature(parent, newDex, layer + 1, direct);
		} else {
			if (parent.getObject().getStructure().isRoot()) {
				return null;
			} else {
				final IGraphicalFeature grandParent = parent.getSourceConnection().getTarget();
				final int newDex = grandParent.getObject().getStructure().getChildIndex(parent.getObject().getStructure());
				return findNextFeature(parent, newDex, layer + 1, direct);
			}
		}

	}

	/**
	 * looks if in the given direction is at least one more feature
	 *
	 * @param siblings
	 * @param dex
	 * @param direct
	 * @return
	 */
	private boolean checkForOneMore(List<IFeatureStructure> siblings, int dex, direction direct) {
		if (direct == direction.right) {
			return (dex < (siblings.size() - 1));
		} else if (direct == direction.left) {
			return dex > 0;
		}
		return false;
	}

}
