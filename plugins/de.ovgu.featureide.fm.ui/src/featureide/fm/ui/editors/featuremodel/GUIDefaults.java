/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.editors.featuremodel;

import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;

/**
 * Defaults colors, fonts and borders for the feature diagram.
 * 
 * @author Thomas Thuem
 */
public interface GUIDefaults {
	
	public static boolean HALF_ARC = true;
	
	public static boolean OR_CIRCLES = false;
	
	//general settings
	
	/**
	 * an Unicode font to be able to display constraints at the feature diagram correctly
	 */
	public static Font DEFAULT_FONT = new Font(null, new FontData("Arial Unicode MS", 8, SWT.NORMAL));
	
	public static Color DIAGRAM_BACKGROUND = ColorConstants.white;

	//features (layer and compound features)
	
	public static Color FEATURE_FOREGROUND = GUIBasics.createColor(0.0, 0.0, 0.0);
	public static Insets FEATURE_INSETS = new Insets(3, 6, 3, 6);//4, 8, 4, 8

	public static Color LAYER_BACKGROUND = GUIBasics.createColor(0.7, 0.7, 1.0);
	public static Color LAYER_BORDER_COLOR = GUIBasics.createBorderColor(LAYER_BACKGROUND);
	public static Border LAYER_BORDER = new LineBorder(LAYER_BORDER_COLOR, 1);

	public static Color COMPOUND_BACKGROUND = GUIBasics.createColor(0.9, 0.9, 1.0);
	public static Color COMPOUND_BORDER_COLOR = GUIBasics.createBorderColor(COMPOUND_BACKGROUND);
	public static Border COMPOUND_BORDER = new LineBorder(COMPOUND_BORDER_COLOR, 1);

	//connections and decorators
	
	public static Color CONNECTION_FOREGROUND = GUIBasics.createColor(0.4, 0.4, 0.4);
	public static Color NEW_CONNECTION_FOREGROUND = GUIBasics.createColor(0.4, 1.0, 0.4);
	public static Color VOID_CONNECTION_FOREGROUND = GUIBasics.createColor(1.0, 0.4, 0.4);
	
	public static Color DECORATOR_FOREGROUND = CONNECTION_FOREGROUND;
	public static Color DECORATOR_BACKGROUND = DIAGRAM_BACKGROUND;
	public static int SOURCE_ANCHOR_DIAMETER = 9;
	public static int TARGET_ANCHOR_DIAMETER = HALF_ARC ? 20 : 50;
	
	//cross-tree constraints
	
	public static Color CONSTRAINT_FOREGROUND = GUIBasics.createColor(0.0, 0.0, 0.0);
	public static Insets CONSTRAINT_INSETS = new Insets(2, 8, 2, 8);
	public static Color CONSTRAINT_BACKGROUND = GUIBasics.createColor(1.0, 1.0, 1.0);
	public static Color CONSTRAINT_BORDER_COLOR = CONSTRAINT_BACKGROUND;
	public static Border CONSTRAINT_BORDER = new LineBorder(CONSTRAINT_BORDER_COLOR, 0);

	//cell editor for renaming features / editing constraints
	
	public static Insets CELL_EDITOR_INSETS = new Insets(0, 4, 0, 4);	
	public static Dimension CELL_EDITOR_MINSIZE = new Dimension(50, 5);	
	
	//space between features for layouting
	
	public static int LAYOUT_MARGIN_X = 20;
	public static int LAYOUT_MARGIN_Y = 40;
	public static int FEATURE_SPACE_X = 5;
	public static int FEATURE_SPACE_Y = 30 + 20;
	public static int CONSTRAINT_SPACE_Y = 5 + 20;
	
}
