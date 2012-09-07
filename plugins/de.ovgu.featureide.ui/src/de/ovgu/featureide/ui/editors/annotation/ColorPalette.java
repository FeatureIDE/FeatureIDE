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
package de.ovgu.featureide.ui.editors.annotation;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

/**
 * TODO description
 * @author Sebastian Krieter
 */
public class ColorPalette {
	public final static int COLOR_COUNT = 10;

	private final static String[] colorNames =
		{"Red", "Orange", "Yellow", "Dark Green", "Light Green", "Cyan", "Light Grey", "Blue", "Magenta", "Pink"};
	private final static float[] hue = new float[COLOR_COUNT];
	private final static float[] brightness = new float[COLOR_COUNT];
	private final static float[] maxSaturation = new float[COLOR_COUNT];
	static {
		float colorStep = 360f / COLOR_COUNT;
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
		return new RGB(hue[index], 
				(1 - transparency) * maxSaturation[index], 
				transparency*(1-brightness[index]) + brightness[index]);
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
		return colorNames[index % COLOR_COUNT];
	}
}
