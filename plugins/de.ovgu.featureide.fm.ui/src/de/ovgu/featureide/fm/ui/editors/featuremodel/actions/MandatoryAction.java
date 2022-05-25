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

import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
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
public class MandatoryAction extends MultipleSelectionAction implements ActionAllowedForRootFeaturesInExternalSubmodel {

	public static final String ID = "de.ovgu.featureide.mandatory";

	public MandatoryAction(Object viewer, IFeatureModelManager featureModelManager) {
		super("Mandatory", viewer, ID, featureModelManager);
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new SetFeatureToMandatoryOperation(featureModelManager, getSelectedFeatures()));
		setChecked(isEveryFeatureMandatory());
	}

	private boolean selectionContainsOptionalFeature() {
		final IFeatureModel featureModel = featureModelManager.getSnapshot();
		for (final String name : featureArray) {
			final IFeatureStructure structure = featureModel.getFeature(name).getStructure();
			if (!structure.isRoot() && structure.getParent().isAnd()) {
				return true;
			}
		}
		return false;
	}

	private boolean isEveryFeatureMandatory() {
		return SetFeatureToMandatoryOperation.isEveryFeatureMandatory(featureModelManager.getSnapshot(), featureArray);
	}

	@Override
	protected void updateProperties() {
		setEnabled(selectionContainsOptionalFeature());
		setChecked(isEveryFeatureMandatory());
	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		for (final Object obj : selection.toArray()) {
			if (!((obj instanceof FeatureEditPart) || (obj instanceof IFeature) || (obj instanceof Feature))) {
				return false;
			}
		}

		// check whether the selection includes no feature from an external submodel
		if ((this instanceof ActionAllowedInExternalSubmodel) || isExternalRootFeature(selection)) {
			return true;
		}

		return false;
	}

}
