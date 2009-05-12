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
package featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.Ellipse;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.geometry.Point;

import featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * A decoration for a feature connection that indicates the mandatory property.
 * 
 * @author Thomas Thuem
 */
public class CircleDecoration extends Ellipse implements RotatableDecoration, GUIDefaults {
	
	public CircleDecoration(boolean fill) {
		super();
		setForegroundColor(DECORATOR_FOREGROUND);
		setBackgroundColor(fill ? DECORATOR_FOREGROUND : DECORATOR_BACKGROUND);
		setSize(SOURCE_ANCHOR_DIAMETER, SOURCE_ANCHOR_DIAMETER);
	}
	
	@Override
	public void setLocation(Point p) {		
		super.setLocation(p.translate(-SOURCE_ANCHOR_DIAMETER/2, -SOURCE_ANCHOR_DIAMETER/2));
	}
	
	public void setReferencePoint(Point p) {
		//nothing to do because this is a circle
	}

}
