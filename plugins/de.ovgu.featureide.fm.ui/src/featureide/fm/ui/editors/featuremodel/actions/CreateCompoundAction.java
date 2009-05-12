/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.ui.editors.featuremodel.actions;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;

/**
 * Creates a new feature with the currently selected features as children.
 * 
 * @author Thomas Thuem
 */
public class CreateCompoundAction extends Action {

	public static String ID = "featureide.createcompound";

	private final FeatureModel featureModel;

	private GraphicalViewerImpl viewer;

	private Feature parent = null;
	
	private LinkedList<Feature> selectedFeatures = new LinkedList<Feature>();
	
	private static ImageDescriptor createImage = PlatformUI.getWorkbench()
	.getSharedImages().getImageDescriptor(
			ISharedImages.IMG_TOOL_NEW_WIZARD);

	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event
					.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	public CreateCompoundAction(GraphicalViewerImpl viewer, FeatureModel featureModel) {
		super("Create compound (above)", createImage);
		this.viewer = viewer;
		this.featureModel = featureModel;
		setEnabled(false);
		viewer.addSelectionChangedListener(listener);
	}

	@Override
	public void run() {
		int number = 0;
		while (featureModel.getFeatureNames().contains("NewCompound" + ++number));
		Feature newCompound = new Feature(featureModel, "NewCompound" + number);
		
		if (parent != null) {
			newCompound.setAND(parent.isAnd());
			newCompound.setMultiple(parent.isMultiple());
			
			LinkedList<Feature> newChildren = new LinkedList<Feature>();
			for (Feature feature : parent.getChildren())
				if (selectedFeatures.contains(feature)) {
					if (!newCompound.hasChildren()) 
						newChildren.add(newCompound);
					newCompound.addChild(feature);
				}
				else
					newChildren.add(feature);
			parent.setChildren(newChildren);

			featureModel.addFeature(newCompound);
		}
		else {
			newCompound.addChild(selectedFeatures.getFirst());
			featureModel.addFeature(newCompound);
			featureModel.setRoot(newCompound);
		}
		
		//needed when the user creates a compound feature again on the same selection
		parent = newCompound;
		featureModel.handleModelDataChanged();
		
		//select the new feature
		FeatureEditPart part = (FeatureEditPart) viewer.getEditPartRegistry().get(newCompound);
		viewer.setSelection(new StructuredSelection(part));

		//open the renaming command
		DirectEditManager manager = new FeatureLabelEditManager(part, TextCellEditor.class,
				new FeatureCellEditorLocator(part.getFeatureFigure()), featureModel);
		manager.show();
	}
	
	@SuppressWarnings("unchecked")
	private boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (i.e. ModelEditPart is selected)
		if (selection.size() == 1
				&& selection.getFirstElement() instanceof ModelEditPart)
			return false;

		// check that selected features have the same parent
		selectedFeatures.clear();
		Iterator iter = selection.iterator();
		while (iter.hasNext()) {
			Object editPart = iter.next();
			if (!(editPart instanceof FeatureEditPart))
				continue;
			Feature feature = ((FeatureEditPart) editPart).getFeatureModel();
			if (selectedFeatures.isEmpty())
				parent = feature.getParent();
			else if (parent != feature.getParent())
					return false;
			selectedFeatures.add(feature);
		}
		return !selectedFeatures.isEmpty();
	}
	
}
