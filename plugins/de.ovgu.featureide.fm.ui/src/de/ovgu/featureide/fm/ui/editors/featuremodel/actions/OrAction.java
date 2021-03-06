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

import static de.ovgu.featureide.fm.core.localization.StringTable.OR;

import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ChangeFeatureGroupTypeOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Turns a group type into an Or-group.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class OrAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.or";

	public OrAction(Object viewer, IFeatureModelManager featureModelManager) {
		super(OR, viewer, ID, featureModelManager);
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new ChangeFeatureGroupTypeOperation(ChangeFeatureGroupTypeOperation.OR, feature.getName(), featureModelManager));
	}

	@Override
	protected void updateProperties() {
		final boolean or = feature.getStructure().isOr();
		// setEnabled(connectionSelected && !feature.isRoot() && !or)
		setEnabled(!or && feature.getStructure().hasChildren() && (feature.getStructure().getChildrenCount() > 1));
		setChecked(or);
	}

}
