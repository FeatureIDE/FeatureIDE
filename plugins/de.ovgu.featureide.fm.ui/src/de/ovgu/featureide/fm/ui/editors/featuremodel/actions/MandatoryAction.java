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

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SetFeatureToMandatoryOperation;

/**
 * Turns features in an And-group into mandatory features.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public class MandatoryAction extends MultipleSelectionAction {

	public static final String ID = "de.ovgu.featureide.mandatory";

	public MandatoryAction(Object viewer, IFeatureModelManager featureModelManager) {
		super("Mandatory", viewer, ID, featureModelManager);
	}

	@Override
	public void run() {
		changeMandatoryStatus(isEveryFeatureMandatory());
		setChecked(isEveryFeatureMandatory());
	}

	private boolean selectionContainsOptionalFeature() {
		final IFeatureModel featureModel = featureModelManager.editObject();
		for (final String name : featureArray) {
			final IFeature tempFeature = featureModel.getFeature(name);
			if (!tempFeature.getStructure().isRoot() && tempFeature.getStructure().getParent().isAnd()) {
				return true;
			}
		}
		return false;
	}

	private boolean isEveryFeatureMandatory() {
		final IFeatureModel featureModel = featureModelManager.editObject();
		for (final String name : featureArray) {
			final IFeature tempFeature = featureModel.getFeature(name);
			if (!(tempFeature.getStructure().isMandatory())) {
				return false;
			}
		}
		return true;
	}

	private void changeMandatoryStatus(boolean allMandatory) {
		FeatureModelOperationWrapper.run(new SetFeatureToMandatoryOperation(featureModelManager, allMandatory, getSelectedFeatures()));
	}

	@Override
	protected void updateProperties() {
		setEnabled(selectionContainsOptionalFeature());
		setChecked(isEveryFeatureMandatory());
	}

}
