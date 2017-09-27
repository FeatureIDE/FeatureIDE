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

	Insets ROLE_INSETS2 = new Insets(1, 6, 1, 6);
	Insets ROLE_INSETS = new Insets(3, 6, 3, 6);
	Insets COLLABORATION_INSETS = new Insets(4, 6, 4, 6);
	Insets CLASS_INSETS = new Insets(10, 20, 10, 20);

	int DEFAULT_CLASS_WIDTH = 100;
	int GENERAL_DISTANCE = 8;
	int ROLE_PREFERED_SIZE = 16;
	int GRIDLAYOUT_MARGIN_HEIGHT = 3;
	int GRIDLAYOUT_VERTICAL_SPACING = 1;
	int DEFAULT_UNDERLAYER_HEIGHT = 35;

	Point COLLFIGURE_LOCATION = new Point(16, 16);

	int DEFAULT_INSET_TO_EDGE = 10;

	Color FOREGROUND = ColorConstants.black;
	Font DEFAULT_FONT = new Font(null, new FontData("Arial Unicode MS", 8, SWT.NORMAL));

	Color DIAGRAM_BACKGROUND = ColorConstants.white;

	Color CLASS_BACKGROUND = GUIBasics.createColor(247, 245, 255);
	Color CLASS_BORDER_COLOR = GUIBasics.createBorderColor(CLASS_BACKGROUND);
	Border CLASS_BORDER = new LineBorder(CLASS_BORDER_COLOR, 1);

	/**
	 * This color highlights the class representing the file at the open editor.
	 */
	Color OPEN_CLASS_BACKGROUND = GUIBasics.createColor(235, 230, 255);
	Color OPEN_CLASS_BORDER_COLOR = GUIBasics.createBorderColor(OPEN_CLASS_BACKGROUND);
	Border OPEN_CLASS_BORDER = new LineBorder(OPEN_CLASS_BORDER_COLOR, 1);

	Color COLL_BACKGROUND_SELECTED = GUIBasics.createColor(0.8, 0.8, 1.0);
	Color COLL_BORDER_COLOR_SELECTED = ColorConstants.black;
	Border COLL_BORDER_SELECTED = new LineBorder(COLL_BORDER_COLOR_SELECTED, 2);

	Color COLL_BACKGROUND_UNSELECTED = GUIBasics.createColor(247, 245, 255);
	Color COLL_BORDER_COLOR_UNSELECTED = ColorConstants.black;
	Border COLL_BORDER_UNSELECTED = new LineBorder(COLL_BORDER_COLOR_UNSELECTED, 1);

	Color ROLE_BACKGROUND_SELECTED = COLL_BACKGROUND_SELECTED;
	Color ROLE_BORDER_COLOR_SELECTED = GUIBasics.createBorderColor(ROLE_BACKGROUND_SELECTED);
	Border ROLE_BORDER_SELECTED = new LineBorder(ROLE_BORDER_COLOR_SELECTED, 1);

	Color ROLE_BACKGROUND_UNSELECTED = GUIBasics.createColor(237, 235, 245);
	Color ROLE_BORDER_COLOR_UNSELECTED = GUIBasics.createBorderColor(ROLE_BACKGROUND_UNSELECTED);
	Border ROLE_BORDER_UNSELECTED = new LineBorder(ROLE_BORDER_COLOR_UNSELECTED, 1);

	Color ROLE_FOREGROUND_UNSELECTED = GUIBasics.createColor(41, 41, 41);
	Color ROLE_BACKGROUND = GUIBasics.createColor(241, 241, 241);

	Color DEFAULT_UNDERLAYING_COLOR_1 = GUIBasics.createColor(253, 253, 253);
	Color DEFAULT_UNDERLAYING_COLOR_2 = GUIBasics.createColor(238, 238, 238);

	Color CLASS_BORDER_COLOR_SELECTED = ColorConstants.darkBlue;
	Border CLASS_BORDER_SELECTED = new LineBorder(CLASS_BORDER_COLOR_SELECTED, 2);

	/**
	 * This color highlights the role(selected) representing the file at the open editor.
	 */
	Color OPEN_ROLE_BACKGROUND_SELECTED = ROLE_BACKGROUND_SELECTED;
	// GUIBasics.createColor(180, 180, 255);
	Color OPEN_ROLE_BORDER_COLOR_SELECTED = GUIBasics.createBorderColor(OPEN_ROLE_BACKGROUND_SELECTED);
	Border OPEN_ROLE_BORDER_SELECTED = new LineBorder(OPEN_ROLE_BORDER_COLOR_SELECTED, 1);

	/**
	 * This color highlights the role(selected) representing the file at the open editor.
	 */
	Color OPEN_ROLE_BACKGROUND_UNSELECTED = ROLE_BACKGROUND_UNSELECTED;
	// GUIBasics.createColor(242, 242, 255);
	Color OPEN_ROLE_BORDER_COLOR_UNSELECTED = GUIBasics.createBorderColor(OPEN_ROLE_BACKGROUND_UNSELECTED);
	Border OPEN_ROLE_BORDER_UNSELECTED = new LineBorder(OPEN_ROLE_BORDER_COLOR_UNSELECTED, 1);

	/*
	 * All images should be declared here, so an image can not be created twice.
	 */
	Image IMAGE_CURRENT_CONFIGURATION = UIPlugin.getImage("currentconfiguration.gif");
	Image IMAGE_CONFIGURATION = UIPlugin.getImage("ConfigurationIcon.png");
	Image REFESH_TAB_IMAGE = UIPlugin.getImage("refresh_tab.gif");

	// Collaboration Diagram
	Image IMAGE_NESTED_CLASS = UIPlugin.getImage("nested_class_icon.png");
	Image IMAGE_FIELDS_REFINEMENTS = UIPlugin.getImage("fields_with_refinements.png");
	Image IMAGE_FIELDS_WITHOUT_REFINEMENTS = UIPlugin.getImage("fields_without_refinements.png");
	Image IMAGE_METHODS_REFINEMENTS = UIPlugin.getImage("methods_with_refinements.png");
	Image IMAGE_METHODS_WITHOUT_REFINEMENTS = UIPlugin.getImage("methods_without_refinements.png");
	Image IMAGE_FIELD_PRIVATE = UIPlugin.getImage("field_private_obj.gif");
	Image IMAGE_FIELD_PROTECTED = UIPlugin.getImage("field_protected_obj.gif");
	Image IMAGE_FIELD_PUBLIC = UIPlugin.getImage("field_public_obj.gif");
	Image IMAGE_FIELD_DEFAULT = UIPlugin.getImage("field_default_obj.gif");
	Image IMAGE_METHODE_PRIVATE = UIPlugin.getImage("private_co.png");
	Image IMAGE_METHODE_PROTECTED = UIPlugin.getImage("protected_co.gif");
	Image IMAGE_METHODE_PUBLIC = UIPlugin.getImage("public_co.gif");
	Image IMAGE_METHODE_DEFAULT = UIPlugin.getImage("default_co.png");
	Image IMAGE_METHODE_DEFAULT_CONTRACT = UIPlugin.getImage("default_co_contract.gif");
	Image IMAGE_METHODE_PUBLIC_CONTRACT = UIPlugin.getImage("public_co_contract.gif");
	Image IMAGE_METHODE_PROTECTED_CONTRACT = UIPlugin.getImage("protected_co_contract.gif");
	Image IMAGE_METHODE_PRIVATE_CONTRACT = UIPlugin.getImage("private_co_contract.gif");
	Image IMAGE_AT_CONTRACT = UIPlugin.getImage("aticon_contract.png");
	Image IMAGE_AT_INVARIANT = UIPlugin.getImage("aticon_invariant.png");
	Image IMAGE_AT_WITHOUT_WHITE_BACKGROUND = UIPlugin.getImage("aticon_2.gif");
	Image IMAGE_CLASS = UIPlugin.getImage("class_obj.gif");
	Image IMAGE_FEATURE = UIPlugin.getImage("FeatureIconSmall.ico");
	Image IMAGE_HASH = UIPlugin.getImage("hash.png");
	Image IMAGE_SELECT_ALL = UIPlugin.getImage("select_all_icon.png");
	Image IMAGE_DESELECT_ALL = UIPlugin.getImage("deselect_all_icon.png");
	Image IMAGE_NONE_ICON = UIPlugin.getImage("placeholder_icon.png");
	Image IMAGE_MODIFIERS_NONE = UIPlugin.getImage("access_modifiers_none.png");

	Image IMAGE_SELECT_ALL_MODIFIERS = UIPlugin.getImage("select_all_modifiers.png");
	Image IMAGE_EXPORT_ICON = UIPlugin.getImage("export_wiz.gif");
	Image IMAGE_EXPORT_XML_ICON = UIPlugin.getImage("export_xml.png");
	Image IMAGE_EXPORT_IMAGE_ICON = UIPlugin.getImage("export_image.png");

	// outline icons for haskell

	Image IMAGE_HASKELL_MODULE = UIPlugin.getImage("module.gif");
	Image IMAGE_HASKELL_LAMBDA = UIPlugin.getImage("lambda.gif");
	Image IMAGE_HASKELL_TYPE = UIPlugin.getImage("type.gif");
	Image IMAGE_HASKELL_DATA = UIPlugin.getImage("haskellData.gif");
}
