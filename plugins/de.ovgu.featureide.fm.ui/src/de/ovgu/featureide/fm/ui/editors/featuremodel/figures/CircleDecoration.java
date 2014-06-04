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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.RoundedRectangle;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A decoration for a feature connection that indicates the mandatory property.
 * 
 * @author Thomas Thuem
 */
public class CircleDecoration extends RoundedRectangle implements
		RotatableDecoration, GUIDefaults {

	public CircleDecoration(boolean fill) {
		super();
		Color decoratorForgroundColor = FMPropertyManager.getDecoratorForgroundColor();
		setForegroundColor(decoratorForgroundColor);
		setBackgroundColor(fill ? decoratorForgroundColor : FMPropertyManager.getDecoratorBackgroundColor());
		setSize(SOURCE_ANCHOR_DIAMETER, SOURCE_ANCHOR_DIAMETER);

	}

	@Override
	public void setLocation(Point p) {
		super.setLocation(p.translate(-SOURCE_ANCHOR_DIAMETER / 2,
				-SOURCE_ANCHOR_DIAMETER / 2));
	}

	public void setReferencePoint(Point p) {

	}

}
