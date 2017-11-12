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
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.LayoutSelectionOperation;

/**
 * Action to select the layout for the feature model.
 *
 * @author Marcus Pinnecke (Feature interface)
 */
public class LayoutSelectionAction extends Action {

	public static final String ID = "de.ovgu.featureide.layoutselectionaction";

	private final IGraphicalFeatureModel featureModel;
	private final int newSelectedLayoutAlgorithm;

	public LayoutSelectionAction(IGraphicalFeatureModel featureModel, int newSelectedLayoutAlgorithm) {
		super(FeatureDiagramLayoutHelper.getLayoutLabel(newSelectedLayoutAlgorithm));
		setId(ID);
		this.newSelectedLayoutAlgorithm = newSelectedLayoutAlgorithm;
		this.featureModel = featureModel;
	}

	@Override
	public void run() {
		final LayoutSelectionOperation op =
			new LayoutSelectionOperation(featureModel, newSelectedLayoutAlgorithm, featureModel.getLayout().getLayoutAlgorithm());
		// TODO _interfaces Removed Code
		op.addContext((IUndoContext) featureModel.getFeatureModel().getUndoContext());
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

}
