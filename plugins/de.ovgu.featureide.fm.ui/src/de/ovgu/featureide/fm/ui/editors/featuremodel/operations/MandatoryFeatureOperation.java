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

import static de.ovgu.featureide.fm.core.localization.StringTable.MANDATORY_OPERATION;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * This class is required to set a feature to mandatory. The operation method() returns the operation used to set a single feature to mandatory
 *
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public class MandatoryFeatureOperation extends AbstractFeatureModelOperation {

	public static final String ID = ID_PREFIX + "MandatoryFeatureOperation";

	private final String featureName;

	public MandatoryFeatureOperation(String featureName, IFeatureModelManager featureModelManager) {
		super(featureModelManager, MANDATORY_OPERATION);
		this.featureName = featureName;
	}

	/**
	 * Flips the mandatory value of the feature named featureName, and returns a new {@link FeatureModelOperationEvent} with feature as source and
	 * MANDATORY_CHANGED as event type.
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		feature.getStructure().setMandatory(!feature.getStructure().isMandatory());
		return new FeatureModelOperationEvent(ID, EventType.MANDATORY_CHANGED, feature, null, null);
	}

	/**
	 * Flips the mandatory value of the feature again; thus restoring its original value and reversing the operation.
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		return operation(featureModel);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
