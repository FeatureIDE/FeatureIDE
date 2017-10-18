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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_INCLUDING_SUBFEATURES;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureTreeDeleteOperation;

/**
 * Action to delete a single feature including its sub features
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Marcus Pinnecke (Feature Interface)
 */
public class DeleteAllAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.deleteall";
	private final IFeatureModel featureModel;
	private static ImageDescriptor deleteImage = PlatformUI.getWorkbench().getSharedImages().getImageDescriptor(ISharedImages.IMG_TOOL_DELETE);

	/**
	 *
	 * @param viewer
	 * @param featureModel
	 */
	public DeleteAllAction(Object viewer, IFeatureModel featureModel) {
		super(DELETE_INCLUDING_SUBFEATURES, viewer);
		this.featureModel = featureModel;
		this.viewer = viewer;
		setImageDescriptor(deleteImage);
	}

	@Override
	public void run() {
		final FeatureTreeDeleteOperation op = new FeatureTreeDeleteOperation(featureModel, feature);

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);

		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.actions.SingleSelectionAction #updateProperties()
	 */
	@Override
	protected void updateProperties() {
		setEnabled(!feature.getStructure().isRoot() && feature.getStructure().hasChildren());
		setChecked(false);
	}

}
