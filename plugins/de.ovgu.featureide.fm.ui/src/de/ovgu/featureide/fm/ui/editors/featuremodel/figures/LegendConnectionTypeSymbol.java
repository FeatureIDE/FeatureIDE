/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.XYAnchor;
import org.eclipse.draw2d.geometry.Point;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * represents a symbol for connection types: Mandatory, Optional
 * 
 * @author Fabian Benduhn
 */
public class LegendConnectionTypeSymbol extends PolylineConnection implements
		GUIDefaults {

	private static final int SIZE = 20;

	/**
	 * creates a new connection type symbol
	 * 
	 * @param mandatory
	 *            if true, type will be mandatory. Otherwise, optional.
	 * @param pos
	 *            position of the symbol
	 */
	public LegendConnectionTypeSymbol(boolean mandatory, Point pos) {
		this.setPreferredSize(SIZE, SIZE);

		setForegroundColor(CONNECTION_FOREGROUND);

		RotatableDecoration sourceDecoration = null;

		sourceDecoration = new CircleDecoration(mandatory);

		setTargetAnchor(new XYAnchor(new Point(pos.x + SIZE / 2, pos.y + 0)));
		setSourceAnchor(new XYAnchor(new Point(pos.x + 0, pos.y + SIZE / 2)));
		setSourceDecoration(sourceDecoration);

	}

}
