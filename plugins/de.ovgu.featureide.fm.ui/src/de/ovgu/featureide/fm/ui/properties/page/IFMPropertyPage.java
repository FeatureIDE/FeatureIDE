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
package de.ovgu.featureide.fm.ui.properties.page;


/**
 * This interface provides all labels, tool tips and some values used at the 
 * {@link FMPropertyPage} 
 * 
 * @author Jens Meinicke
 */
public interface IFMPropertyPage {
	static final String DESCRIPTION = "At this page you can define settings for the \"Feature Model Editor\".";

	/************************************************************** 
	 * legend group elements:                                     *
	 **************************************************************/
	/* legend group labels: */
	static final String LEGEND_GROUP_TEXT = "Legend";
	static final String LEGEND_HIDE_LABEL = "Hide legend";
	static final String LEGEND_LANGUAGE_LABEL = "Language";
	static final String LEGEND_BORDER_LABEL = "Border color:";
	static final String LEGEND_BACKGROUND_LABEL = "Background color:";

	/* legend group tool tips: */
	static final String LEGEND_BACKGROUND__TIP = "Sets the background color of the legend";
	static final String LEGEND_BORDER_TIP = "Sets the border color of the legend";
	
	/************************************************************** 
	 * spaces group elements:                                     *
	 **************************************************************/	
	/* spaces group labels: */
	static final String SPACES_GROUP_TEXT = "Spaces";
	static final String SPACES_MARGIN_X = "Border distance horizontally:";
	static final String SPACES_MARGIN_Y = "Border distance vertically:";
	static final String SPACES_FEATURE_X = "Feature space horizontally:";
	static final String SPACES_FEATURE_Y = "Feature space vertically:";
	static final String SPACES_CONSTRAINT = "Constaint space:";
	
	/* spaces group tool tips: */
	static final String SPACES_TIP_MARGIN_X = "Minimum horizontally distance to border";
	static final String SPACES_TIP_MARGIN_Y = "Minimum vertically distance to border";
	static final String SPACES_TIP_FEATURE_X = "Horizontally space between two features";
	static final String SPACES_TIP_FEATURE_Y = "Vertically space between two features";
	static final String SPACES_TIP_CONSTRIANT = "Space between the model and the first constraint";
	
	/*
	 *  with this values adjusting the shown spaces, 
	 *  it is more logical for the user
	 */
	static final int SPECES_FEATURE_X_ADJUST = 20;
	static final int SPECES_CONSTRAIT_ADJUST = 21;
	
	/************************************************************** 
	 * color group elements:                                      *
	 **************************************************************/
	/* color group labels: */
	static final String COLOR_GROUP_TEXT = "Colors";
	static final String COLOR_DIAGRAM_LABEL = "Diagram background:";
	static final String COLOR_CONCRETE_LABEL = "Concrete feature color:";
	static final String COLOR_ABSTRACT_LABEL = "Abstract feature color:";
//	static final String COLOR_HIDDEN = "Hidden feature background color:";
	static final String COLOR_DEAD = "Dead feature color:";
	static final String COLOR_CONSTRAINT = "Constraind color:";
	static final String COLOR_WARNING = "Warning color:";
	static final String COLOR_CONNECTION = "Connection color:";
	
	/* color group tool tips: */ // TODO @Jens: tool tips
//	static final String COLOR_HIDDEN_TIP = "";
	static final String COLOR_DEAD_TIP = "";
	static final String COLOR_CONNECTION_TIP = "";
	static final String COLOR_CONSTRAINT_TIP = "";
	static final String COLOR_WARNING_TIP = "";
	static final String COLOR_BACKGROUND_TIP = "";
	static final String COLOR_CONCRETE_TIP = "";
	static final String COLOR_ABSTRACT_TIP = "";
	
	/************************************************************** 
	 * extensions group elements:                                 *
	 **************************************************************/
	/* extensions group labels: */
	static final String EXTENSIONS_GROUP_TEXT = "Extensions";
}
