/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelLayout;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;

/**
 * @author David Halm
 * @author Patrick Sulkowski
 */
public class ShowHiddenFeaturesOperation extends AbstractFeatureModelOperation {

	public ShowHiddenFeaturesOperation(FeatureModel featureModel) {
		super(featureModel, "Show Hidden Features");
	}

	@Override
	protected void redo() {
		final FeatureModelLayout layout = featureModel.getLayout();
		layout.showHiddenFeatures(!layout.showHiddenFeatures());		
		FeatureUIHelper.showHiddenFeatures(layout.showHiddenFeatures(),featureModel);
	}

	@Override
	protected void undo() {
		redo();
	}

}
