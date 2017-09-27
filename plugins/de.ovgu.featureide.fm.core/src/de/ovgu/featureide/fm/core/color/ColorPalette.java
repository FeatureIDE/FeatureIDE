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
package de.ovgu.featureide.fm.core.color;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

/**
 * Holds a number of color constants and according color names.
 *
 * @author Sebastian Krieter
 */
public class ColorPalette {

	public final static int COLOR_COUNT = 10;

	private final static float[] hue = new float[COLOR_COUNT];
	private final static float[] brightness = new float[COLOR_COUNT];
	private final static float[] maxSaturation = new float[COLOR_COUNT];
	static {
		final float colorStep = 360f / COLOR_COUNT;
		for (int i = 0; i < COLOR_COUNT; i++) {
			hue[i] = i * colorStep;
			brightness[i] = 1f;
			maxSaturation[i] = 1f;
		}

		hue[0] = 358f;
		hue[1] = 34f;
		hue[8] = 290f;
		hue[9] = 326f;

		brightness[3] = 0.70f;
		brightness[5] = 0.95f;
		brightness[6] = 0.70f;
		brightness[7] = 0.70f;
		brightness[9] = 0.70f;

		maxSaturation[0] = 0.9f;
		maxSaturation[6] = 0.0f;
	}

	public static RGB getRGB(int index, float transparency) {
		index %= COLOR_COUNT;
		return new RGB(hue[index], (1 - transparency) * maxSaturation[index], (transparency * (1 - brightness[index])) + brightness[index]);
	}

	public static RGB getRGB(int index) {
		return getRGB(index, 1f);
	}

	public static Color getColor(int index, float transparency) {
		return new Color(null, getRGB(index, transparency));
	}

	public static Color getColor(int index) {
		return getColor(index, 1f);
	}

	public static String getColorName(int index) {
		return FeatureColor.getColor(index).toString().replace('_', ' ');
	}

	public static Color toSwtColor(FeatureColor featureColor) {
		float transparency = 0.4f;
		int valTemp = featureColor.value;

		if (valTemp < 0) {
			valTemp = 0;
			transparency = 1;
		}

		return new Color(null, ColorPalette.getRGB(valTemp, transparency));
	}

}
