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
package de.ovgu.featureide.fm.ui.editors.featuremodel;

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
	
	public static boolean HALF_ARC = false;
	
	public static boolean OR_CIRCLES = false;
	
	//general settings
	
	/**
	 * an Unicode font to be able to display constraints at the feature diagram correctly
	 */
	public static Font DEFAULT_FONT = new Font(null, new FontData("Arial Unicode MS", 8, SWT.NORMAL));
	
	public static Color DIAGRAM_BACKGROUND = ColorConstants.white;

	//concrete, hidden, dead and abstract features
	
	public static Color FEATURE_FOREGROUND = GUIBasics.createColor(0.0, 0.0, 0.0);
	public static Insets FEATURE_INSETS = new Insets(3, 6, 3, 6);//4, 8, 4, 8

	public static Color CONCRETE_BACKGROUND = GUIBasics.createColor(0.8, 0.8, 1.0);
	public static Color CONCRETE_BORDER_COLOR = GUIBasics.createBorderColor(CONCRETE_BACKGROUND);
	public static Border CONCRETE_BORDER = new LineBorder(CONCRETE_BORDER_COLOR, 1);
	public static Color CONCRETE_SELECTED_BORDER_COLOR = CONCRETE_BORDER_COLOR;
	public static Border CONCRETE_SELECTED_BORDER = new LineBorder(CONCRETE_SELECTED_BORDER_COLOR, 3);

	public static Color ABSTRACT_BACKGROUND = GUIBasics.createColor(0.95, 0.95, 1.0);
	public static Color ABSTRACT_BORDER_COLOR = GUIBasics.createBorderColor(ABSTRACT_BACKGROUND);
	public static Border ABSTRACT_BORDER = new LineBorder(ABSTRACT_BORDER_COLOR, 1);
	public static Color ABSTRACT_SELECTED_BORDER_COLOR = ABSTRACT_BORDER_COLOR;
	public static Border ABSTRACT_SELECTED_BORDER = new LineBorder(ABSTRACT_SELECTED_BORDER_COLOR, 3);
	
	public static Color HIDDEN_FOREGROUND = GUIBasics.createColor(0.4, 0.4, 0.4);
	public static Color HIDDEN_BACKGROUND = GUIBasics.createColor(0.8, 0.8, 1.0);
	public static Color HIDDEN_BORDER_COLOR = GUIBasics.createBorderColor(HIDDEN_BACKGROUND);
	public static Border HIDDEN_BORDER = new LineBorder(HIDDEN_BORDER_COLOR, 1, 2);
	public static Border HIDDEN_BORDER_LEGEND = new LineBorder(DIAGRAM_BACKGROUND, 1, SWT.LINE_DOT);
	public static Border HIDDEN_SELECTED_BORDER = new LineBorder(HIDDEN_BORDER_COLOR, 3, 2);
	
	public static Color DEAD_BACKGROUND = GUIBasics.createColor(1.0, 0.8, 0.8);
	public static Color DEAD_BORDER_COLOR = GUIBasics.createBorderColor(DEAD_BACKGROUND);
	public static Border DEAD_BORDER = new LineBorder(DEAD_BORDER_COLOR, 1);
	public static Color DEAD_SELECTED_BORDER_COLOR = DEAD_BORDER_COLOR;
	public static Border DEAD_SELECTED_BORDER = new LineBorder(DEAD_BORDER_COLOR, 3);
	
	//connections and decorators
	
	public static Color CONNECTION_FOREGROUND = GUIBasics.createColor(0.4, 0.4, 0.4);
	public static Color NEW_CONNECTION_FOREGROUND = GUIBasics.createColor(0.4, 1.0, 0.4);
	public static Color VOID_CONNECTION_FOREGROUND = GUIBasics.createColor(1.0, 0.4, 0.4);
	
	public static Color DECORATOR_FOREGROUND = CONNECTION_FOREGROUND;
	public static Color DECORATOR_BACKGROUND = DIAGRAM_BACKGROUND;
	public static int SOURCE_ANCHOR_DIAMETER = 9;
	@SuppressWarnings("all")
	public static int TARGET_ANCHOR_DIAMETER = HALF_ARC ? 20 : 40;
	
	//cross-tree constraints
	
	public static Color CONSTRAINT_FOREGROUND = FEATURE_FOREGROUND;
	public static Insets CONSTRAINT_INSETS = new Insets(2, 8, 2, 8);
	public static Color CONSTRAINT_BACKGROUND = GUIBasics.createColor(1.0, 1.0, 1.0);
	public static Color CONSTRAINT_BORDER_COLOR = CONSTRAINT_BACKGROUND;
	public static Border CONSTRAINT_BORDER = new LineBorder(CONSTRAINT_BORDER_COLOR, 0);
	public static Color CONSTRAINT_SELECTED_BORDER_COLOR = GUIBasics.createBorderColor(CONSTRAINT_BACKGROUND);
	public static Border CONSTRAINT_SELECTED_BORDER = new LineBorder(CONSTRAINT_SELECTED_BORDER_COLOR, 3);
		
	//false constraints
	
	public static Color WARNING_BACKGROUND = GUIBasics.createColor(1.0, 1.0, 0.6);	
	public static Color ERROR_BACKGROUND = DEAD_BACKGROUND;	
	
	//cell editor for renaming features / editing constraints
	
	public static Insets CELL_EDITOR_INSETS = new Insets(0, 4, 0, 4);	
	public static Dimension CELL_EDITOR_MINSIZE = new Dimension(50, 5);	
	
	//space between features for layouting
	
	public static int LAYOUT_MARGIN_X = 20;
	public static int LAYOUT_MARGIN_Y = 40;
	public static int FEATURE_SPACE_X = 5;
	public static int FEATURE_SPACE_Y = 30 + 20;
	public static int CONSTRAINT_SPACE_Y = 5 + 20;
	
	//legend
	public static int LEGEND_WIDTH = 95;
	public static Color LEGEND_FOREGROUND = FEATURE_FOREGROUND;
	public static Color LEGEND_BACKGROUND = DIAGRAM_BACKGROUND;
	public static Color LEGEND_BORDER_COLOR = LEGEND_FOREGROUND;
	public static Border LEGEND_BORDER = new LineBorder(LEGEND_BORDER_COLOR, 1);

}
