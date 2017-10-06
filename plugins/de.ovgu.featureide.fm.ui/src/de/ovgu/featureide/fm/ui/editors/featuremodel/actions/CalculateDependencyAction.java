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

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_DEPENDENCY;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CalculateDependencyOperation;

/**
 * Action to calculate implicit dependencies of a sub feature model after selecting a feature and choosing to "calculate implicit dependencies". This feature
 * will be the root of the new sub feature model.
 *
 * @author "Ananieva Sofia"
 */
public class CalculateDependencyAction extends Action {

	/**
	 * The ID which is used to return the respective action after a context menu selection.
	 */
	public static final String ID = "de.ovgu.featureide.calculatedependency";

	/**
	 * The complete feature model.
	 */
	private final IFeatureModel featureModel;

	/**
	 * The selected feature which will be used as new root.
	 */
	private final LinkedList<IFeature> selectedFeatures = new LinkedList<IFeature>();

	/**
	 * The listener which remembers the selection and checks whether it is valid.
	 */
	private final ISelectionChangedListener listener = new ISelectionChangedListener() {
		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	/**
	 * Constructor.
	 *
	 * @param viewer
	 * @param featureModel The complete feature model
	 */
	public CalculateDependencyAction(Object viewer, IFeatureModel featureModel) {
		super(CALCULATE_DEPENDENCY);
		this.featureModel = featureModel;
		setId(ID);
		setEnabled(false);
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer).addSelectionChangedListener(listener);
		}
	}

	/**
	 * Performs the operation of calculating sub feature model dependencies. The selected feature is root of the new sub feature mode.
	 */
	@Override
	public void run() {
		if (selectedFeatures.size() != 1) {
			throw new RuntimeException("Calculate dependencies for multiple selected features is not supported.");
		}
		final CalculateDependencyOperation op = new CalculateDependencyOperation(featureModel, selectedFeatures.get(0));

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Checks if selection is valid, i.e. selection is not empty, not root and a feature from the feature model tree.
	 *
	 * @param selection the selected feature from the feature model tree
	 * @return true if valid selection, else false
	 */
	private boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (i.e. ModelEditPart is selected)
		if ((selection.size() == 1) && (selection.getFirstElement() instanceof ModelEditPart)) {
			return false;
		}

		selectedFeatures.clear();
		final Iterator<?> iter = selection.iterator();
		while (iter.hasNext()) {
			final Object editPart = iter.next();
			if (!(editPart instanceof FeatureEditPart) && !(editPart instanceof IFeature)) {
				continue;
			}
			IFeature feature;

			if (editPart instanceof FeatureEditPart) {
				feature = ((FeatureEditPart) editPart).getModel().getObject();
			} else {
				feature = (IFeature) editPart;
			}

			selectedFeatures.add(feature);
		}

		final boolean res = !selectedFeatures.isEmpty();

		// permit selection to be root of the origin feature model
		if (res) {
			final String s = selectedFeatures.getFirst().toString();
			if (s.equals(FeatureUtils.getRoot(featureModel).toString())) {
				return false;
			}
		}
		return res;
	}
}
