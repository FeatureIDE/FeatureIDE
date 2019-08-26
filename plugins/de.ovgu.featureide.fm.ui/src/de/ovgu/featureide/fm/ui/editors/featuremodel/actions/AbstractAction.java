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

import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SetFeatureToAbstractOperation;

/**
 * Action to mark a feature as abstract.
 *
 * @author Marcus Pinnecke (Feature Interface)
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public class AbstractAction extends MultipleSelectionAction {

	public static final String ID = "de.ovgu.featureide.abstract";

	public AbstractAction(Object viewer, IFeatureModelManager featureModelManager) {
		super("Abstract", viewer, ID, featureModelManager);
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new SetFeatureToAbstractOperation(featureModelManager, getSelectedFeatures()));
		setChecked(isEveryFeatureAbstract());
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
		// A selection of features is considered abstract if every feature is abstract.
		setChecked(isEveryFeatureAbstract());
	}

	private boolean isEveryFeatureAbstract() {
		return SetFeatureToAbstractOperation.isEveryFeatureAbstract(featureModelManager.getSnapshot(), featureArray);
	}

}
