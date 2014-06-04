/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureCreateCompoundOperation;

/**
 * Creates a new feature with the currently selected features as children.
 * 
 * @author Thomas Thuem
 */
public class CreateCompoundAction extends Action {

	public static final String ID = "de.ovgu.featureide.createcompound";

	private final FeatureModel featureModel;

	private Object viewer;

	private Feature parent = null;
	
	private LinkedList<Feature> selectedFeatures = new LinkedList<Feature>();
	
	private Object diagramEditor;

	private static ImageDescriptor createImage = PlatformUI.getWorkbench()
			.getSharedImages()
			.getImageDescriptor(ISharedImages.IMG_OBJ_ADD);

	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event
					.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	

	public CreateCompoundAction(Object viewer,
			FeatureModel featureModel, Object diagramEditor) {
		super("Create Feature Above", createImage);
		this.viewer = viewer;
		this.featureModel = featureModel;
		this.diagramEditor = diagramEditor;

		setEnabled(false);
		if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);
		} else {
			((TreeViewer) viewer).addSelectionChangedListener(listener);
		}
	}

	@Override
	public void run() {
		FeatureCreateCompoundOperation op = new FeatureCreateCompoundOperation(
				viewer, parent, featureModel, selectedFeatures, diagramEditor);
		op.addContext((IUndoContext) featureModel.getUndoContext());

		try {
			PlatformUI.getWorkbench().getOperationSupport()
					.getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

	private boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (i.e. ModelEditPart is selected)
		if (selection.size() == 1
				&& (selection.getFirstElement() instanceof ModelEditPart 
						))
			return false;

		// check that selected features have the same parent
		selectedFeatures.clear();
		Iterator<?> iter = selection.iterator();
		while (iter.hasNext()) {
			Object editPart = iter.next();
			if (!(editPart instanceof FeatureEditPart) && !(editPart instanceof Feature))
				continue;
			Feature feature;
			
			if (editPart instanceof FeatureEditPart)
				feature = ((FeatureEditPart) editPart).getFeature();
			else
				feature = (Feature) editPart;
			
			if (selectedFeatures.isEmpty())
				parent = feature.getParent();
			else if (parent != feature.getParent())
				return false;
			selectedFeatures.add(feature);
		}
		return !selectedFeatures.isEmpty();
	}

}
