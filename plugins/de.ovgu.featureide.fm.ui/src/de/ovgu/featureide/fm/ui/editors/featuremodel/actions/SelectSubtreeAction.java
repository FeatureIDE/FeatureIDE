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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_SUBTREE;

import java.util.List;
import java.util.Map;

import org.eclipse.gef.EditPart;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramViewer;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Selects the whole subtree of a selected feature
 *
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class SelectSubtreeAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.selectSubtree";
	private static ImageDescriptor createImage;

	public SelectSubtreeAction(Object viewer, IFeatureModelManager featureModelManager) {
		super(SELECT_SUBTREE, viewer, ID, featureModelManager);
	}

	@Override
	public void run() {
		if (viewer instanceof FeatureDiagramViewer) {
			final FeatureDiagramViewer featureDiagramViewer = (FeatureDiagramViewer) viewer;
			final FeatureEditPart part = (FeatureEditPart) featureDiagramViewer.getFocusEditPart();
			final Map<?, ?> editPartRegistry = featureDiagramViewer.getEditPartRegistry();
			final List<IGraphicalFeature> children = part.getModel().getGraphicalChildren();
			selectChildren(editPartRegistry, children, featureDiagramViewer);
		}
	}

	private void selectChildren(Map<?, ?> editPartRegistry, List<IGraphicalFeature> children, FeatureDiagramViewer viewer) {
		for (final IGraphicalFeature child : children) {
			final EditPart childPart = (EditPart) editPartRegistry.get(child);
			viewer.appendSelection(childPart);
			selectChildren(editPartRegistry, child.getGraphicalChildren(), viewer);
		}
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		return super.isValidSelection(selection);
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
	}

}
