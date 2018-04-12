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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_SIBLINGS;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SetSiblingsToCollapsedOperation;

/**
 * Collapses all siblings of the selected feature if the parent is either an OR or an ALTERNATIVE.
 *
 * @author Maximilian Kühl
 */
public class CollapseSiblingsAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.collapsefeatures";

	private final IGraphicalFeatureModel graphicalFeatureModel;

	/**
	 * Collapse siblings should not be accessible for root.
	 */
	private final ISelectionChangedListener listener = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection));
			if (isValidSelection(selection)) {
				if (selection.getFirstElement() instanceof FeatureEditPart) {
					if (getSelectedFeature().getStructure().isRoot() || (getSelectedFeature().getStructure().getParent().getChildrenCount() == 1)) {
						setEnabled(false);
					} else {
						setEnabled(true);
					}
				}
			}
		}
	};

	/**
	 * @param label Description of this operation to be used in the menu
	 * @param feature feature on which this operation will be executed
	 *
	 */
	public CollapseSiblingsAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		super(COLLAPSE_SIBLINGS, viewer, ID);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/collapse.gif"));
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

		final SetSiblingsToCollapsedOperation op = new SetSiblingsToCollapsedOperation(feature, graphicalFeatureModel);

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}

	}

	@Override
	protected void updateProperties() {}
}
