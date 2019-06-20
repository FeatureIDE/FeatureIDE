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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.HIDE_OPERATION;

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to set Features hidden. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Paul Westphal
 * @author Chico Sundermann
 */
public class SetFeatureToHiddenOperation extends MultiFeatureModelOperation {

	public static final String ID = ID_PREFIX + "SetFeatureToHiddenOperation";

	private final boolean allHidden;

	public SetFeatureToHiddenOperation(IFeatureModelManager featureModelManager, boolean allHidden, List<String> featureNames) {
		super(featureModelManager, HIDE_OPERATION, featureNames);
		this.allHidden = allHidden;
	}

	@Override
	protected String getID() {
		return ID;
	}

	@Override
	protected void createSingleOperations(IFeatureModel featureModel) {
		for (final String name : featureNames) {
			final IFeature tempFeature = featureModel.getFeature(name);
			if (allHidden || !tempFeature.getStructure().isHidden()) {
				final HideFeatureOperation op = new HideFeatureOperation(name, featureModelManager);
				operations.add(op);
			}
		}
	}
}
