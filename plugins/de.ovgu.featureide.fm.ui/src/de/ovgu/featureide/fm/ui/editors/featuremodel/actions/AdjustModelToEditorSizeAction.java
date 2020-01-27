/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AdjustModelToEditorSizeOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * TODO description
 *
 * @author Maximilian Kühl
 * @author Joshua Sprey
 */
public class AdjustModelToEditorSizeAction extends AFeatureModelAction {

	public static final String ID = "de.ovgu.featureide.adjustmodeltoeditor";

	private FeatureDiagramEditor editor;
	private final IGraphicalFeatureModel graphicalFeatureModel;

	public AdjustModelToEditorSizeAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel, String title) {
		super(title, ID, graphicalFeatureModel.getFeatureModelManager());
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/monitor_obj.gif"));
		if (viewer instanceof FeatureDiagramEditor) {
			editor = (FeatureDiagramEditor) viewer;
		}
		this.graphicalFeatureModel = graphicalFeatureModel;
	}

	@Override
	public void run() {
		final IFeature root = FeatureUtils.getRoot(featureModelManager.getSnapshot());
		if (root == null) {
			return;
		}
		FeatureModelOperationWrapper.run(new AdjustModelToEditorSizeOperation(graphicalFeatureModel, editor));
		if (editor != null) {
			final IGraphicalFeature graphicalRoot = FeatureUIHelper.getGraphicalFeature(root, editor.getGraphicalFeatureModel());
			editor.getViewer().centerPointOnScreen(graphicalRoot.getObject());
		}
	}

}
