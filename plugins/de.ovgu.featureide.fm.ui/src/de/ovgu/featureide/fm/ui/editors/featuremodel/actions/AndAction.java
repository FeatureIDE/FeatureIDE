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

import static de.ovgu.featureide.fm.core.localization.StringTable.AND;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;

/**
 * Turns a group type into an And-group.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class AndAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.and";

	private final IFeatureModel featureModel;

	public AndAction(Object viewer, IFeatureModel featureModel) {
		super(AND, viewer, ID);
		this.featureModel = featureModel;
	}

	@Override
	public void run() {
		final ChangeFeatureGroupTypeOperation op = new ChangeFeatureGroupTypeOperation(ChangeFeatureGroupTypeOperation.AND, feature, featureModel);
		op.addContext((IUndoContext) featureModel.getUndoContext());

		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	@Override
	protected void updateProperties() {
		final boolean and = feature.getStructure().isAnd();
		setEnabled(!and && feature.getStructure().hasChildren());
		setChecked(and);
	}

}
