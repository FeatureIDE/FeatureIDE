/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.FOLD_OUT_FEATURE;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FoldOutOperation;

/**
 * TODO description
 * 
 * @author Joshua Sprey
 * @author Enis Belli
 */
public class FoldOutAction extends Action {

	//LinkedList<IFeature> selectedFeatures = new LinkedList<IFeature>();

	IFeatureModel featureModel;
	IFeature selectedFeature;

	public FoldOutAction(Object viewer, IFeatureModel featureModel) {
		super(FOLD_OUT_FEATURE);
		this.featureModel = featureModel;
		setEnabled(false);
		// TODO Auto-generated constructor stub
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer).addSelectionChangedListener(listener);
		}
	}

	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	@Override
	public void run() {
		FoldOutOperation op = new FoldOutOperation(featureModel, selectedFeature);
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	private boolean isValidSelection(IStructuredSelection selection) {
		// check selected only one element
		if (selection.size() == 1 && !(selection.getFirstElement() instanceof ModelEditPart)) {
			Object editPart = selection.getFirstElement();
			if (editPart instanceof FeatureEditPart) {
				selectedFeature = ((FeatureEditPart) editPart).getFeature().getObject();
				return true;
			} else if (editPart instanceof IFeature) {
				selectedFeature = (IFeature) editPart;
				return true;
			}
		}
		return false;
	}

}
