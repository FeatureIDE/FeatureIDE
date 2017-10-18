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

import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_HIDDEN_FEATURES;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Specifies whether hidden features are shown.
 *
 * @author David Halm
 * @author Patrick Sulkowski
 * @author Marcus Pinnecke
 */
public class ShowHiddenFeaturesOperation extends AbstractGraphicalFeatureModelOperation {

	public ShowHiddenFeaturesOperation(IGraphicalFeatureModel featureModel) {
		super(featureModel, SHOW_HIDDEN_FEATURES);
	}

	@Override
	public FeatureIDEEvent operation() {
		graphicalFeatureModel.getLayout().showHiddenFeatures(!graphicalFeatureModel.getLayout().showHiddenFeatures());
		// TODO add specific handling in FeatureDiagram editor so not everything needs to be reloaded
		return new FeatureIDEEvent(graphicalFeatureModel, EventType.MODEL_DATA_CHANGED);
	}

	@Override
	public FeatureIDEEvent inverseOperation() {
		return operation();
	}

}
