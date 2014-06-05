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
package de.ovgu.featureide.fm.ui.editors.featuremodel;

import javax.annotation.CheckReturnValue;

import org.eclipse.draw2d.LineBorder;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;

/**
 * Implements some basic graphical methods.
 * 
 * @author Thomas Thuem
 */
@CheckReturnValue
public class GUIBasics {

	public static Color createColor(int r, int g, int b) {
		return new Color(null, r, g, b);
	}

	public static Color createColor(double r, double g, double b) {
		return new Color(null, (int) (r*255), (int) (g*255), (int) (b*255));
	}

	public static Color createBorderColor(Color color) {
		int r = (int) (color.getRed()*0.75);
		int g = (int) (color.getGreen()*0.75);
		int b = (int) (color.getBlue()*0.75);
		return new Color(null, r, g, b);
	}

	public static LineBorder createLineBorder(Color color, int width, int style) {
		return new LineBorder(color, width, style);
	}

	public static LineBorder createLineBorder(Color color, int width) {
		return new LineBorder(color, width);
	}
	
	public static boolean unicodeStringTest(Font swtFont, String s) {
		FontData fd = swtFont.getFontData()[0];
		java.awt.Font awtFont = new java.awt.Font(fd.getName(),0,fd.getHeight());
		for (int i = 0; i < s.length(); i++)
			if (!awtFont.canDisplay(s.charAt(i)))
				return false;
		return true;
	}
	
}
