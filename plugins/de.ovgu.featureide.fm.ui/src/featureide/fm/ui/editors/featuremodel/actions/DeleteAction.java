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

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ActionFactory;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;

/**
 * Deletes the selected features and moves their unselected children upwards.
 * 
 * @author Thomas Thuem
 */
public class DeleteAction extends Action {

	public static String ID = ActionFactory.DELETE.getId();

	private static ImageDescriptor deleteImage = PlatformUI.getWorkbench()
			.getSharedImages()
			.getImageDescriptor(ISharedImages.IMG_TOOL_DELETE);

	private final GraphicalViewerImpl viewer;

	private final FeatureModel featureModel;

	private ISelectionChangedListener listener = new ISelectionChangedListener() {
		public void selectionChanged(SelectionChangedEvent event) {
			IStructuredSelection selection = (IStructuredSelection) event
					.getSelection();
			setEnabled(isValidSelection(selection));
		}
	};

	public DeleteAction(GraphicalViewerImpl viewer, FeatureModel featureModel) {
		super("Delete", deleteImage);
		this.viewer = viewer;
		this.featureModel = featureModel;
		setEnabled(false);
		viewer.addSelectionChangedListener(listener);
	}

	@SuppressWarnings("unchecked")
	@Override
	public void run() {
		IStructuredSelection selection = (IStructuredSelection) viewer
				.getSelection();
		Iterator iter = selection.iterator();
		while (iter.hasNext()) {
			Object editPart = iter.next();
			if (!(editPart instanceof FeatureEditPart))
				continue;
			Feature feature = ((FeatureEditPart) editPart)
					.getFeatureModel();
			if (feature == featureModel.getRoot())
				featureModel.replaceRoot(featureModel.getRoot().removeLastChild());
			else
				featureModel.deleteFeature(feature);
		}
		featureModel.handleModelDataChanged();
	}

	@SuppressWarnings("unchecked")
	private boolean isValidSelection(IStructuredSelection selection) {
		// check empty selection (i.e. ModelEditPart is selected)
		if (selection.size() == 1
				&& selection.getFirstElement() instanceof ModelEditPart)
			return false;

		//check that a possibly new root can be determined unique
		Feature root = featureModel.getRoot();
		Feature newRoot = root;
		LinkedList<Feature> features = new LinkedList<Feature>(featureModel.getFeatures());
		Iterator iter = selection.iterator();
		while (iter.hasNext()) {
			Object editPart = iter.next();
			if (!(editPart instanceof FeatureEditPart))
				continue;
			Feature feature = ((FeatureEditPart) editPart).getFeatureModel();
			if (feature == root) {
				if (root.getChildrenCount() != 1)
					return false;
				newRoot = root.getFirstChild();
				if (!newRoot.hasChildren())
					return false;
			}
			features.remove(feature);
		}
		
		//check that the only child of a deleted root is not deleted too
		if (root != newRoot && !features.contains(newRoot))
			return false;
		
		//check that the root has at least one child
		return features.size() > 1;
	}
}
