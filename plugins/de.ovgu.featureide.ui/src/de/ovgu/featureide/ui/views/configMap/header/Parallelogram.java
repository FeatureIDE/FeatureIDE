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
package de.ovgu.featureide.ui.views.configMap.header;

/**
 * A Parallelogram Hitbox.
 *
 * <pre> skew ________|___ / | / height / | / /__________|/ x/y width
 *
 * </pre>
 *
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class Parallelogram {

	private float width, height, skew, x, y;

	public Parallelogram() {
		this(1, 1, 0);
	}

	public Parallelogram(float width, float height, float skew) {
		this.width = width;
		this.height = height;
	}

	public float getX() {
		return x;
	}

	public float getY() {
		return y;
	}

	public void setLocation(float x, float y) {
		this.x = x;
		this.y = y;
	}

	public float getWidth() {
		return width;
	}

	public void setWidth(float width) {
		this.width = width;
	}

	public float getHeight() {
		return height;
	}

	public void setHeight(float height) {
		this.height = height;
	}

	public float getSkew() {
		return skew;
	}

	public void setSkew(float skew) {
		this.skew = skew;
	}

	public boolean containsPoint(float px, float py) {
		final float totalWidth = width + skew;
		// check if point is in bounding rectangular
		final boolean inXAxis = (x <= px) && (px <= (x + totalWidth));
		final boolean inYAxis = (y <= py) && (py <= (y + height));

		if (inXAxis && inYAxis) {
			// skew = 0 <=> parallelogram is rectangle
			if (skew == 0) {
				return true;
			}

			// check if the point is not in one of the triangles at the left and right of the parallelogram
			final float gradient = height / skew;
			final float dx = px - x;
			return (py <= (gradient * dx)) && ((gradient * (dx - width)) <= py);
		}

		return false;
	}

}
