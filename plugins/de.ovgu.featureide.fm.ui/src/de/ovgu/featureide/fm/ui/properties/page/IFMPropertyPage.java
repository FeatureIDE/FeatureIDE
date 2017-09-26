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
package de.ovgu.featureide.fm.ui.properties.page;

import static de.ovgu.featureide.fm.core.localization.StringTable.COLORS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CUSTOM_BORDER_COLOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXTENSIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.HORIZONTALLY_SPACE_BETWEEN_TWO_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.LEGEND;
import static de.ovgu.featureide.fm.core.localization.StringTable.MINIMUM_HORIZONTALLY_DISTANCE_TO_BORDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.MINIMUM_VERTICALLY_DISTANCE_TO_BORDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_BACKGROUND_COLOR_OF_THE_LEGEND;
import static de.ovgu.featureide.fm.core.localization.StringTable.SETS_THE_BORDER_COLOR_OF_THE_LEGEND;
import static de.ovgu.featureide.fm.core.localization.StringTable.SPACES;
import static de.ovgu.featureide.fm.core.localization.StringTable.SPACE_BETWEEN_THE_MODEL_AND_THE_FIRST_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.VERTICALLY_SPACE_BETWEEN_TWO_FEATURES;

/**
 * This interface provides all labels, tool tips and some values used at the {@link FMPropertyPage}
 *
 * @author Jens Meinicke
 */
public interface IFMPropertyPage {

	static final String DESCRIPTION = "At this page you can define settings for the \"Feature Model Editor\".";

	/**************************************************************
	 * legend group elements: *
	 **************************************************************/
	/* legend group labels: */
	static final String LEGEND_GROUP_TEXT = LEGEND;
	static final String LEGEND_HIDE_LABEL = "Hide legend:";
	static final String LEGEND_LANGUAGE_LABEL = "Language:";
	static final String LEGEND_BORDER_LABEL = "Border color:";
	static final String LEGEND_BACKGROUND_LABEL = "Background color:";

	/* legend group tool tips: */
	static final String LEGEND_BACKGROUND__TIP = SETS_THE_BACKGROUND_COLOR_OF_THE_LEGEND;
	static final String LEGEND_BORDER_TIP = SETS_THE_BORDER_COLOR_OF_THE_LEGEND;

	/**************************************************************
	 * spaces group elements: *
	 **************************************************************/
	/* spaces group labels: */
	static final String SPACES_GROUP_TEXT = SPACES;
	static final String SPACES_MARGIN_X = "Border distance horizontally:";
	static final String SPACES_MARGIN_Y = "Border distance vertically:";
	static final String SPACES_FEATURE_X = "Feature space horizontally:";
	static final String SPACES_FEATURE_Y = "Feature space vertically:";
	static final String SPACES_CONSTRAINT = "Constaint space:";

	/* spaces group tool tips: */
	static final String SPACES_TIP_MARGIN_X = MINIMUM_HORIZONTALLY_DISTANCE_TO_BORDER;
	static final String SPACES_TIP_MARGIN_Y = MINIMUM_VERTICALLY_DISTANCE_TO_BORDER;
	static final String SPACES_TIP_FEATURE_X = HORIZONTALLY_SPACE_BETWEEN_TWO_FEATURES;
	static final String SPACES_TIP_FEATURE_Y = VERTICALLY_SPACE_BETWEEN_TWO_FEATURES;
	static final String SPACES_TIP_CONSTRIANT = SPACE_BETWEEN_THE_MODEL_AND_THE_FIRST_CONSTRAINT;

	/*
	 * with this values adjusting the shown spaces, it is more logical for the user
	 */
	static final int SPECES_FEATURE_X_ADJUST = 20;
	static final int SPECES_CONSTRAIT_ADJUST = 21;

	/**************************************************************
	 * color group elements: *
	 **************************************************************/
	/* color group labels: */
	static final String COLOR_GROUP_TEXT = COLORS;
	static final String COLOR_DIAGRAM_LABEL = "Diagram background:";
	static final String COLOR_CONCRETE_LABEL = "Concrete feature color:";
	static final String COLOR_ABSTRACT_LABEL = "Abstract feature color:";
	// static final String COLOR_HIDDEN = "Hidden feature background color:";
	static final String COLOR_ERROR = "Error color:";
	static final String COLOR_CONSTRAINT = "Constraint color:";
	static final String COLOR_WARNING = "Warning color:";
	static final String COLOR_CONNECTION = "Connection color:";
	static final String HIDE_BORDER_COLOR = CUSTOM_BORDER_COLOR;
	static final String COLOR_BORDER = "Feature border color:";

	/* color group tool tips: */
	// static final String COLOR_HIDDEN_TIP = "";
	static final String COLOR_DEAD_TIP = "";
	static final String COLOR_CONNECTION_TIP = "";
	static final String COLOR_CONSTRAINT_TIP = "";
	static final String COLOR_WARNING_TIP = "";
	static final String COLOR_BACKGROUND_TIP = "";
	static final String COLOR_CONCRETE_TIP = "";
	static final String COLOR_ABSTRACT_TIP = "";
	static final String COLOR_CHECKBOX_TIP = "enabled: custom color selectable\ndisabled: standard color";
	static final String COLOR_BORDER_TIP = "";

	/**************************************************************
	 * extensions group elements: *
	 **************************************************************/
	/* extensions group labels: */
	static final String EXTENSIONS_GROUP_TEXT = EXTENSIONS;
}
