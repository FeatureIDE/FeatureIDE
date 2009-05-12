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

import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TextCellEditor;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureCellEditorLocator;
import featureide.fm.ui.editors.featuremodel.commands.renaming.FeatureLabelEditManager;
import featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Creates a new feature as a child of the currently selected feature.
 * 
 * @author Thomas Thuem
 */
public class CreateLayerAction extends SingleSelectionAction {

	public static String ID = "featureide.createlayer";

	private static ImageDescriptor createImage = PlatformUI.getWorkbench()
			.getSharedImages().getImageDescriptor(
					ISharedImages.IMG_TOOL_NEW_WIZARD);

	private final FeatureModel featureModel;

	public CreateLayerAction(GraphicalViewerImpl viewer, FeatureModel featureModel) {
		super("Create layer (below)", viewer);
		setImageDescriptor(createImage);
		this.featureModel = featureModel;
	}

	@Override
	public void run() {
		int number = 0;
		while (featureModel.getFeatureNames().contains("NewLayer" + ++number));
		Feature newFeature = new Feature(featureModel, "NewLayer" + number);
		featureModel.addFeature(newFeature);
		feature.addChild(newFeature);
		featureModel.handleModelDataChanged();

		//select the new feature
		FeatureEditPart part = (FeatureEditPart) viewer.getEditPartRegistry().get(newFeature);
		viewer.setSelection(new StructuredSelection(part));

		//open the renaming command
		DirectEditManager manager = new FeatureLabelEditManager(part, TextCellEditor.class,
				new FeatureCellEditorLocator(part.getFeatureFigure()), featureModel);
		manager.show();
	}
	
	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		return super.isValidSelection(selection) && getSelectedFeature().canHaveChildren();
	}

	@Override
	protected void updateProperties() {
		setEnabled(!connectionSelected);
		setChecked(false);
	}

}
