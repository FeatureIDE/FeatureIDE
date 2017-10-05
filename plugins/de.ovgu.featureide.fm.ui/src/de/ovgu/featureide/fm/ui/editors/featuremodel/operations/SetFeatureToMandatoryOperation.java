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

import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_MANDATORY;
import static de.ovgu.featureide.fm.core.localization.StringTable.SET_FEATURE_OPTIONAL;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * Operation with functionality to set a Feature mandatory/concrete. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class SetFeatureToMandatoryOperation extends AbstractFeatureModelOperation {

	private static final String LABEL_MANDATORY = SET_FEATURE_MANDATORY;
	private static final String LABEL_OPTIONAL = SET_FEATURE_OPTIONAL;
	private final IFeature feature;

	/**
	 */
	public SetFeatureToMandatoryOperation(IFeature feature, IFeatureModel featureModel) {
		super(featureModel, getLabel(feature));
		this.feature = feature;
	}

	/**
	 * @param feature
	 * @return
	 */
	private static String getLabel(IFeature feature) {
		if (feature.getStructure().isMandatory()) {
			return LABEL_OPTIONAL;
		} else {
			return LABEL_MANDATORY;
		}
	}

	@Override
	protected FeatureIDEEvent operation() {
		final boolean isMandatory = feature.getStructure().isMandatory();
		feature.getStructure().setMandatory(!isMandatory);
		return new FeatureIDEEvent(feature, EventType.MANDATORY_CHANGED, isMandatory, !isMandatory);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		return operation();
	}

}
