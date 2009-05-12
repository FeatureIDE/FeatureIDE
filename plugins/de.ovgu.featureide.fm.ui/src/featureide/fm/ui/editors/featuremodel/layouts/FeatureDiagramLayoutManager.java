/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.editors.featuremodel.layouts;

import java.util.List;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;

import featureide.fm.core.Constraint;
import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.FeatureUIHelper;
import featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Calculates locations for all features in the feature diagram.
 * 
 * @author Thomas Thuem
 */
abstract public class FeatureDiagramLayoutManager implements GUIDefaults {
	
	int controlWidth = 10;
	
	int controlHeight = 10;

	abstract public void layout(FeatureModel featureModel);

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
			FeatureUIHelper.setLocation(constraint,new Point(x,y));
			y += size.height;
		}		
	}

}
