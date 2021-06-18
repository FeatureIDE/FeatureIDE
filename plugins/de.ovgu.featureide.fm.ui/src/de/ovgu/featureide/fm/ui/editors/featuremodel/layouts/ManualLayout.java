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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using their saved Positions.
 *
 * @author David Halm
 * @author Patrick Sulkowski
 * @author Marcus Pinnecke
 */
public class ManualLayout extends FeatureDiagramLayoutManager {

	public ManualLayout() {
		super();
	}

	@Override
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		for (final IGraphicalFeature feature : featureModel.getVisibleFeatures()) {
			setLocation(feature, feature.getLocation());
		}
		if (featureModel.getLayout().isAutoLayoutConstraints()) {
			final IGraphicalFeature root =
				FeatureUIHelper.getGraphicalFeature(FeatureUtils.getRoot(featureModel.getFeatureModelManager().getSnapshot()), featureModel);
			// Calculate yoffset as the position of the lowest visible feature + its height.
			int yoffset = FMPropertyManager.getLayoutMarginY();

			for (final IGraphicalFeature feat : featureModel.getVisibleFeatures()) {
				if (yoffset < feat.getLocation().y) {
					yoffset += FMPropertyManager.getFeatureSpaceY();
				}
			}

			layoutConstraints(yoffset, featureModel.getVisibleConstraints(), getBounds(root));
		} else {
			for (final IGraphicalConstraint constraint : featureModel.getVisibleConstraints()) {
				constraint.setLocation(constraint.getLocation());
			}
		}
	}

}
