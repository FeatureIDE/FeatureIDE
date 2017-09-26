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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.geometry.Rectangle;

/**
 * Workaround for {@link Graphics}.
 *
 * @author Jens Meinicke
 */
public class Draw2dHelper {

	/**
	 * Draws a filled circle inside the rectangle.<br> Workaround for the method {@link Graphics#fillArc(Rectangle, int, int)} as it seems to be broken.
	 *
	 * @param graphics The graphics to draw in.
	 * @param bounds The bounds of the circle.
	 */
	public static void fillCircle(Graphics graphics, Rectangle bounds) {
		fillArc(graphics, bounds, 0, 360);
	}

	/**
	 * Draws a filled arc inside the rectangle.<br> Workaround for the method {@link Graphics#fillArc(Rectangle, int, int)} as it seems to be broken.
	 *
	 * @param graphics The graphics to draw in.
	 * @param bounds The bounds of the arc.
	 * @param offset The start angle of the arc.
	 * @param length The length of the arc.
	 */
	public static void fillArc(Graphics graphics, Rectangle bounds, int offset, int length) {
		fillArc(graphics, bounds.x, bounds.y, bounds.width, bounds.height, offset, length);
	}

	/**
	 * Draws a filled arc inside the rectangle.<br> Workaround for the method {@link Graphics#fillArc(Rectangle, int, int)} as it seems to be broken.
	 *
	 * @param graphics The graphics to draw in.
	 * @param offset The start angle of the arc.
	 * @param length The length of the arc.
	 */
	public static void fillArc(Graphics graphics, int x, int y, int width, int height, int offset, int length) {
		graphics.fillArc(x, y, width + 1, height + 1, offset, length);
	}
}
