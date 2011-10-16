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
package de.ovgu.featureide.ui.views.collaboration;

import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;

/**
 * Colors, Fonts, for Collaboration View
 * 
 * @author Constanze Adler
 */
public interface GUIDefaults {
	
	public static Insets ROLE_INSETS 			 	  = new Insets(3, 6, 3, 6);
	public static Insets COLLABORATION_INSETS 		  = new Insets(4, 6, 4, 6);
	public static Insets CLASS_INSETS 		     	  = new Insets(10, 20, 10, 20);
	
	public static Color FOREGROUND    		  	 	  = ColorConstants.black;
	public static Font DEFAULT_FONT 			 	  = new Font(null, new FontData("Arial Unicode MS", 8, SWT.NORMAL));
	
	public static Color DIAGRAM_BACKGROUND 		 	  = ColorConstants.white;
	
	public static Color CLASS_BACKGROUND   		 	  = GUIBasics.createColor(247, 245, 255);
	public static Color CLASS_BORDER_COLOR	  		  = GUIBasics.createBorderColor(CLASS_BACKGROUND);
	public static Border CLASS_BORDER				  = new LineBorder(CLASS_BORDER_COLOR, 1);

	/**
	 * This color highlights the class representing the file at the open editor.
	 */
	public static Color OPEN_CLASS_BACKGROUND   	  = GUIBasics.createColor(235, 230, 255);
	public static Color OPEN_CLASS_BORDER_COLOR	  	  = GUIBasics.createBorderColor(OPEN_CLASS_BACKGROUND);
	public static Border OPEN_CLASS_BORDER			  = new LineBorder(OPEN_CLASS_BORDER_COLOR, 1);
	
	public static Color COLL_BACKGROUND_SELECTED 	  = GUIBasics.createColor(0.8, 0.8, 1.0);
	public static Color COLL_BORDER_COLOR_SELECTED	  = GUIBasics.createBorderColor(COLL_BACKGROUND_SELECTED);
	public static Border COLL_BORDER_SELECTED	 	  = new LineBorder(COLL_BORDER_COLOR_SELECTED, 1);
	
	public static Color COLL_BACKGROUND_UNSELECTED 	  = GUIBasics.createColor(247, 245, 255);
	public static Color COLL_BORDER_COLOR_UNSELECTED  = GUIBasics.createBorderColor(COLL_BACKGROUND_UNSELECTED);
	public static Border COLL_BORDER_UNSELECTED	 	  = new LineBorder(COLL_BORDER_COLOR_UNSELECTED, 1);
		
	public static Color ROLE_BACKGROUND_SELECTED	  = GUIBasics.createColor(204, 204, 255);
	public static Color ROLE_BORDER_COLOR_SELECTED	  = GUIBasics.createBorderColor(ROLE_BACKGROUND_SELECTED);
	public static Border ROLE_BORDER_SELECTED		  = new LineBorder(ROLE_BORDER_COLOR_SELECTED, 1);
	
	public static Color ROLE_BACKGROUND_UNSELECTED    = GUIBasics.createColor(237, 235, 245);
	public static Color ROLE_BORDER_COLOR_UNSELECTED  = GUIBasics.createBorderColor(ROLE_BACKGROUND_UNSELECTED);
	public static Border ROLE_BORDER_UNSELECTED	 	  = new LineBorder(ROLE_BORDER_COLOR_UNSELECTED, 1);

	/**
	 * This color highlights the role(selected) representing the file at the open editor.
	 */
	public static Color OPEN_ROLE_BACKGROUND_SELECTED	= ROLE_BACKGROUND_SELECTED; 
			//GUIBasics.createColor(180, 180, 255);
	public static Color OPEN_ROLE_BORDER_COLOR_SELECTED	= GUIBasics.createBorderColor(OPEN_ROLE_BACKGROUND_SELECTED);
	public static Border OPEN_ROLE_BORDER_SELECTED		= new LineBorder(OPEN_ROLE_BORDER_COLOR_SELECTED, 1);
	
	/**
	 * This color highlights the role(selected) representing the file at the open editor.
	 */
	public static Color OPEN_ROLE_BACKGROUND_UNSELECTED		= ROLE_BACKGROUND_UNSELECTED; 
			//GUIBasics.createColor(242, 242, 255);
	public static Color OPEN_ROLE_BORDER_COLOR_UNSELECTED	= GUIBasics.createBorderColor(OPEN_ROLE_BACKGROUND_UNSELECTED);
	public static Border OPEN_ROLE_BORDER_UNSELECTED		= new LineBorder(OPEN_ROLE_BORDER_COLOR_UNSELECTED, 1);
		
}
