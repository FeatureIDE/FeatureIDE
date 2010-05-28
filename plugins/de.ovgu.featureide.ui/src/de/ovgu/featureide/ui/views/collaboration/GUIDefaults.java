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
package de.ovgu.featureide.ui.views.collaboration;

import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;

/**
 * Colors, Fonts, for Collaboration View
 * 
 * @author Constanze Adler
 */
public interface GUIDefaults {
	
	public static Color DIAGRAM_BACKGROUND 		 = ColorConstants.white;
	public static Color CLASS_BACKGROUND   		 = new Color(null,247, 245, 255);// new Color(null,251, 250, 174);
	public static Color COLL_BACKGROUND_ODD 	 = new Color(null,233, 229, 255);
	public static Color COLL_BACKGROUND_EVEN 	 = new Color(null,168, 154, 255);
	public static Color FOREGROUND    		  	 = ColorConstants.black;
	public static Font DEFAULT_FONT = new Font(null, new FontData("Arial Unicode MS", 8, SWT.NORMAL));
	
	public static Insets ROLE_INSETS = new Insets(3, 6, 3, 6);
	public static Insets COLLABORATION_INSETS = new Insets(4, 6, 4, 6);
	public static Insets CLASS_INSETS = new Insets(10, 20, 10, 20);
	public static Border ROLE_BORDER = new LineBorder(ColorConstants.black,1);
}
