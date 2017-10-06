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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_ALL;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CollapseAllOperation;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;

/**
 * collapses/expand all features in the given feature model
 *
 * @author Joshua Sprey
 * @author Enis Belli
 */
public class CollapseAllAction extends Action {

	public static final String ID = "de.ovgu.featureide.collapseall";

	private final IGraphicalFeatureModel graphicalFeatureModel;

	public CollapseAllAction(IGraphicalFeatureModel graphicalFeatureModel) {
		super(COLLAPSE_ALL);
		this.graphicalFeatureModel = graphicalFeatureModel;
		setId(ID);
		setImageDescriptor(FmOutlinePageContextMenu.IMG_COLLAPSE);
	}

	@Override
	public void run() {
		final CollapseAllOperation op = new CollapseAllOperation(graphicalFeatureModel, true);
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

}
