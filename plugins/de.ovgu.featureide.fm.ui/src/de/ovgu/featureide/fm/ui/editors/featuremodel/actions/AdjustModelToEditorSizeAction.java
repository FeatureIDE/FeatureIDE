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

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AdjustModelToEditorSizeOperation;

/**
 * TODO description
 *
 * @author Maximilian Kühl
 * @author Joshua Sprey
 */
public class AdjustModelToEditorSizeAction extends Action {

	public static final String ID = "de.ovgu.featureide.adjustmodeltoeditor";

	private FeatureDiagramEditor editor;
	private final IGraphicalFeatureModel graphicalFeatureModel;

	public AdjustModelToEditorSizeAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel, String title) {
		super(title);
		setId(ID);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/monitor_obj.gif"));
		if (viewer instanceof FeatureDiagramEditor) {
			editor = (FeatureDiagramEditor) viewer;
		}
		this.graphicalFeatureModel = graphicalFeatureModel;
	}

	@Override
	public void run() {
		final IFeature root = graphicalFeatureModel.getFeatureModel().getStructure().getRoot().getFeature();
		if (root == null) {
			return;
		}
		final AdjustModelToEditorSizeOperation op = new AdjustModelToEditorSizeOperation(graphicalFeatureModel, editor);
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		if (editor != null) {
			final IGraphicalFeature graphicalRoot = FeatureUIHelper.getGraphicalFeature(root, editor.getGraphicalFeatureModel());
			editor.getViewer().centerPointOnScreen(graphicalRoot.getObject());
		}
	}

}
