package de.ovgu.featureide.ui.color;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

/**
 * 
 * @author Sebastian Krieter
 */
public class ColorPalette {
	private final static int COLOR_COUNT = 10;

	private final static String[] colorNames =
		{"Red", "Orange", "Yellow", "Dark Green", "Light Green", "Cyan", "Light Grey", "Dark Blue", "Magenta", "Pink"};
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
		
		brightness[3] = 0.7f;
		brightness[6] = 0.7f;
		brightness[7] = 0.7f;
		brightness[9] = 0.7f;
		
		maxSaturation[0] = 0.9f;
		maxSaturation[6] = 0.0f;
	}

	public static RGB getRGB(int index, float transparency) {
		return new RGB(hue[index % hue.length], 
				(1 - transparency) * maxSaturation[index], 
				transparency*(1-brightness[index % hue.length]) + brightness[index % hue.length]);
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
		return colorNames[index];
	}
}
