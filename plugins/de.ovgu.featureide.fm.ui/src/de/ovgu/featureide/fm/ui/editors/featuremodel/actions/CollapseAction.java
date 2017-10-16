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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_FEATURE;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SetFeatureToCollapseOperation;

/**
 * collapse the current selected feature
 *
 * @author Joshua Sprey
 * @author Enis Belli
 */
public class CollapseAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.collapse";

	private final IGraphicalFeatureModel graphicalFeatureModel;

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection));
			if (isValidSelection(selection)) {
				if (selection.getFirstElement() instanceof FeatureEditPart) {
					setEnabled(true);
				} else {
					setEnabled(false);
				}
			} else {
				setEnabled(false);
			}
		}
	};

	public CollapseAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		super(COLLAPSE_FEATURE, viewer);
		this.graphicalFeatureModel = graphicalFeatureModel;
		setEnabled(false);
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer).addSelectionChangedListener(listener);
		}
	}

	@Override
	public void run() {

		final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
		setChecked(graphicalFeature.isCollapsed());
		// setChecked(feature.getStructure().isCollapsed());
		final SetFeatureToCollapseOperation op = new SetFeatureToCollapseOperation(feature, graphicalFeatureModel);

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}

	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
		// setChecked(feature.getStructure().isCollapsed());

		final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
		setChecked(graphicalFeature.isCollapsed());
	}

}
