/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.List;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Calculates locations for all features in the feature diagram.
 * 
 * @author Thomas Thuem
 */
abstract public class FeatureDiagramLayoutManager implements GUIDefaults {

	int controlWidth = 10;

	int controlHeight = 10;

	public void layout(FeatureModel featureModel) {
		layoutFeatureModel(featureModel);
		if(featureModel.hasLegendAutoLayout())layoutLegend(featureModel);
	}

	abstract public void layoutFeatureModel(FeatureModel featureModel);

	public void setControlSize(int width, int height) {
		this.controlWidth = width;
		this.controlHeight = height;
	}

	void layout(int yoffset, List<Constraint> constraints) {
		int y = yoffset + CONSTRAINT_SPACE_Y;
		for (int i = 0; i < constraints.size(); i++) {
			Constraint constraint = constraints.get(i);
			Dimension size = FeatureUIHelper.getSize(constraint);
			int x = (controlWidth - size.width) / 2;
			FeatureUIHelper.setLocation(constraint, new Point(x, y));
			y += size.height;
		}
	}

	/**
	 * sets the position of the legend to the right-bottom of the features
	 */
	private void layoutLegend(FeatureModel featureModel) {
		int maxX = 0;
		int maxY = 0;

		for (Feature c : featureModel.getFeatures()) {
			int nextX = FeatureUIHelper.getLocation(c).x
					+ FeatureUIHelper.getSize(c).width;
			if (nextX > maxX)
				maxX = nextX;
			int nextY = FeatureUIHelper.getLocation(c).y;
			if (nextY > maxY)
				maxY = nextY + FeatureUIHelper.getSize(c).height;

		}
		Feature root = featureModel.getRoot();
		int rootY = FeatureUIHelper.getLocation(root).y;
		if (maxY < rootY + LEGEND_HEIGHT) {
			for (Constraint c : featureModel.getConstraints()) {
				int nextX = FeatureUIHelper.getLocation(c).x
						+ FeatureUIHelper.getSize(c).width;
				if (nextX > maxX)
					maxX = nextX;
			}
		}

		featureModel.setLegendPos(maxX + FEATURE_SPACE_X, rootY);
	}
}
