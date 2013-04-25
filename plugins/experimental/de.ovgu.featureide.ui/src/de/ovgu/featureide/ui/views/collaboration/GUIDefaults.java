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
package de.ovgu.featureide.ui.views.collaboration;

import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Colors, Fonts, for Collaboration View
 * 
 * @author Constanze Adler
 */
public interface GUIDefaults {
	
	public static Insets ROLE_INSETS2 			 	  = new Insets(1, 6, 1, 6);
	public static Insets ROLE_INSETS 			 	  = new Insets(3, 6, 3, 6);
	public static Insets COLLABORATION_INSETS 		  = new Insets(4, 6, 4, 6);
	public static Insets CLASS_INSETS 		     	  = new Insets(10, 20, 10, 20);
	
	public static final int GENERAL_DISTANCE             	 =  8;
	public static final int ROLE_PREFERED_SIZE         		 = 16;
	public static final int GRIDLAYOUT_MARGIN_HEIGHT    	 =  3; 
	public static final int GRIDLAYOUT_VERTICAL_SPACING 	 =  1; 
	public static final int DEFAULT_UNDERLAYER_HEIGHT	 	 = 35;
	
	public static final Point COLLFIGURE_LOCATION		= new Point(16, 16);
	
	public static final int DEFAULT_INSET_TO_EDGE	  = 10;
	
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
	public static Color COLL_BORDER_COLOR_SELECTED	  = ColorConstants.black;
	public static Border COLL_BORDER_SELECTED	 	  = new LineBorder(COLL_BORDER_COLOR_SELECTED, 2);
	
	public static Color COLL_BACKGROUND_UNSELECTED 	  = GUIBasics.createColor(247, 245, 255);
	public static Color COLL_BORDER_COLOR_UNSELECTED  = ColorConstants.black;
	public static Border COLL_BORDER_UNSELECTED	 	  = new LineBorder(COLL_BORDER_COLOR_UNSELECTED, 1);
		
	public static Color ROLE_BACKGROUND_SELECTED	  = COLL_BACKGROUND_SELECTED;
	public static Color ROLE_BORDER_COLOR_SELECTED	  = GUIBasics.createBorderColor(ROLE_BACKGROUND_SELECTED);
	public static Border ROLE_BORDER_SELECTED		  = new LineBorder(ROLE_BORDER_COLOR_SELECTED, 1);
	
	public static Color ROLE_BACKGROUND_UNSELECTED    = GUIBasics.createColor(237, 235, 245);
	public static Color ROLE_BORDER_COLOR_UNSELECTED  = GUIBasics.createBorderColor(ROLE_BACKGROUND_UNSELECTED);
	public static Border ROLE_BORDER_UNSELECTED	 	  = new LineBorder(ROLE_BORDER_COLOR_UNSELECTED, 1);
	
	public static Color ROLE_FOREGROUND_UNSELECTED    = GUIBasics.createColor(41, 41, 41);
	public static Color ROLE_BACKGROUND    			  = GUIBasics.createColor(241, 241, 241);
	
	public static Color DEFAULT_UNDERLAYING_COLOR_1   = GUIBasics.createColor(253, 253, 253);
	public static Color DEFAULT_UNDERLAYING_COLOR_2   = GUIBasics.createColor(238, 238, 238);
	
	public static Color  CLASS_BORDER_COLOR_SELECTED  = ColorConstants.darkBlue;
	public static Border CLASS_BORDER_SELECTED	 	  = new LineBorder(CLASS_BORDER_COLOR_SELECTED, 2);
	
	

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
		
	/*
	 * All images should be declared here, so an image can not be created twice.
	 */
	public static final Image IMAGE_CURRENT_CONFIGURATION = UIPlugin.getImage("currentconfiguration.gif");
	public static final Image IMAGE_CONFIGURATION = UIPlugin.getImage("ConfigurationIcon.png");
	public static final Image REFESH_TAB_IMAGE = UIPlugin.getImage("refresh_tab.gif");

	// Collaboration Diagram 
	public static final Image IMAGE_FIELD_PRIVATE = UIPlugin.getImage("field_private_obj.gif");
	public static final Image IMAGE_FIELD_PROTECTED = UIPlugin.getImage("field_protected_obj.gif");
	public static final Image IMAGE_FIELD_PUBLIC = UIPlugin.getImage("field_public_obj.gif");
	public static final Image IMAGE_FIELD_DEFAULT = UIPlugin.getImage("field_default_obj.gif");
	public static final Image IMAGE_METHODE_PRIVATE = UIPlugin.getImage("private_co.gif");
	public static final Image IMAGE_METHODE_PROTECTED = UIPlugin.getImage("protected_co.gif");
	public static final Image IMAGE_METHODE_PUBLIC = UIPlugin.getImage("public_co.gif");
	public static final Image IMAGE_METHODE_DEFAULT =  UIPlugin.getImage("default_co.gif");
	public static final Image IMAGE_CLASS = UIPlugin.getImage("class_obj.gif");
	public static final Image IMAGE_FEATURE = UIPlugin.getImage("FeatureIconSmall.ico");
	public static final Image IMAGE_HASH = UIPlugin.getImage("hash.png");
}
