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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.ABSTRACT_OPERATION;

import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to set Features abstract. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Paul Westphal
 * @author Chico Sundermann
 */
public class SetFeatureToAbstractOperation extends ComposedFeatureModelOperation {

	public static final String ID = ID_PREFIX + "SetFeatureToAbstractOperation";

	public SetFeatureToAbstractOperation(IFeatureModelManager featureModelManager, List<String> featureNames) {
		super(featureModelManager, ABSTRACT_OPERATION, featureNames);
	}

	@Override
	protected String getID() {
		return ID;
	}

	@Override
	protected void createSingleOperations(IFeatureModel featureModel) {
		final boolean allAbstract = isEveryFeatureAbstract(featureModel, featureNames);
		for (final String name : featureNames) {
			final IFeature tempFeature = featureModel.getFeature(name);
			if (allAbstract || !tempFeature.getStructure().isAbstract()) {
				final AbstractFeatureOperation op = new AbstractFeatureOperation(name, featureModelManager);
				operations.add(op);
			}
		}
	}

	public static boolean isEveryFeatureAbstract(IFeatureModel featureModel, List<String> featureNames) {
		return featureNames.stream().allMatch(featureName -> featureModel.getFeature(featureName).getStructure().isAbstract());
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
