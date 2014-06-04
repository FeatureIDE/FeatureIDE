/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Operation with functionality to set a Feature hidden. Enables undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 */
public class FeatureSetHiddenOperation extends AbstractFeatureModelOperation {

	private static final String LABEL_NOT_HIDDEN = "Set Feature Not-Hidden";
	private static final String LABEL_HIDDEN = "Set Feature Hidden";
	private Feature feature;

	public FeatureSetHiddenOperation(Feature feature, FeatureModel featureModel) {
		super(featureModel, getLabel(feature));
		this.feature = feature;
	}

	private static String getLabel(Feature feature) {
		if (feature.isHidden()) {
			return LABEL_NOT_HIDDEN;
		} else {
			return LABEL_HIDDEN;
		}
	}

	@Override
	protected void redo() {
		feature.setHidden(!feature.isHidden());
	}

	@Override
	protected void undo() {
		redo();
	}

}
