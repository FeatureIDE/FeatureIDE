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
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * TODO represents a symbol for group types: And, Or, Alternative
 * 
 * @author Fabian Benduhn
 */
public class LegendGroupTypeSymbol extends PolylineConnection implements
		GUIDefaults {

	private static final int SIZE = 15;

	@Override
	public boolean useLocalCoordinates() {
		return true;

	}

	/**
	 * creates a new Grouptype symbol
	 * 
	 * @param decoration
	 *            if false, symbol will be of type: And
	 * @param fill
	 *            if decoration is true, symbol will be of type: Or. Otherwise
	 *            Alternative. Ignored if decoration is false;
	 * @param point
	 *            the point in absolute coordinates
	 * @param ref
	 *            the position of its parent that will be used to calculate the
	 *            actual positions
	 */
	public LegendGroupTypeSymbol(boolean decoration, boolean fill, Point point,
			Point ref) {
		this.setSize(new Dimension(SIZE, SIZE));
		RotatableDecoration sourceDecoration = null;
		Point p1 = new Point(ref.x + point.x + SIZE, ref.y + point.y + SIZE);
		Point p2 = new Point(ref.x + point.x + SIZE / 2, ref.y + point.y + 0);
		Point p3 = new Point(ref.x + point.x + 0, ref.y + point.y + SIZE);

		sourceDecoration = new LegendRelationDecoration(fill, new Point(point.x
				+ SIZE, point.y + SIZE));

		setTargetAnchor(new XYAnchor(p2));

		setSourceAnchor(new XYAnchor(p3));

		if (decoration)
			setTargetDecoration(sourceDecoration);
		PolylineConnection p = new PolylineConnection();
		p.setSourceAnchor(new XYAnchor(p2));
		p.setTargetAnchor(new XYAnchor(p1));
		this.add(p);
		this.setValid(true);
		setForegroundColor(CONNECTION_FOREGROUND);
	}
}
