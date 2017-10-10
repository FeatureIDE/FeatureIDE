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
package de.ovgu.featureide.fm.core.io.xml;

import static de.ovgu.featureide.fm.core.localization.StringTable.AUTO;
import static de.ovgu.featureide.fm.core.localization.StringTable.REDUNDANT;
import static de.ovgu.featureide.fm.core.localization.StringTable.TAUTOLOGY;

/**
 * Provides the XML tags for {@link XmlFeatureModelReader} and {@link XmlFeatureModelWriter}.
 *
 * @author Jens Meinicke
 */
public interface XMLFeatureModelTags {

	static final String PROPERTIES = "properties";
	static final String FEATURE_MODEL = "featureModel";
	static final String STRUCT = "struct";
	static final String FEATURE_ORDER = "featureOrder";
	static final String CONSTRAINTS = "constraints";
	static final String CONSTRAINT = "constraint";
	static final String COLLAPSED = "collapsed";
	static final String FEATURES = "features";
	static final String CHOSEN_LAYOUT_ALGORITHM = "chosenLayoutAlgorithm";
	static final String C = "c";
	static final String TRUE = "true";
	static final String FEATURE = "feature";
	static final String OR = "or";
	static final String ALT = "alt";
	static final String AND = "and";
	static final String DESCRIPTION = "description";
	static final String USER_DEFINED = "userDefined";
	static final String VAR = "var";
	static final String IMP = "imp";
	static final String EQ = "eq";
	static final String CONJ = "conj";
	static final String DISJ = "disj";
	static final String COORDINATES = "coordinates";
	static final String CALCULATE_FEATURES = "Features";
	static final String CALCULATE_REDUNDANT = REDUNDANT;
	static final String CALCULATE_TAUTOLOGY = TAUTOLOGY;
	static final String CALCULATE_CONSTRAINTS = de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINTS;
	static final String CALCULATE_AUTO = AUTO;
	static final String NAME = "name";
	static final String FALSE = "false";
	static final String SHOW_HIDDEN_FEATURES = "showHiddenFeatures";
	static final String SHOW_COLLAPSED_CONSTRAINTS = "showCollapsedConstraints";
	static final String HIDE_LEGEND = "hideLegend";
	static final String SHOW_SHORT_NAMES = "showShortNames";
	static final String HORIZONTAL_LAYOUT = "horizontalLayout";
	static final String RULE = "rule";
	static final String UNKNOWN = "unknown";
	static final String ATMOST1 = "atmost1";
	static final String ATTRIBUTE = "attribute";
	static final String UNIT = "unit";
	static final String TYPE = "type";
	static final String VALUE = "value";
	static final String RECURSIVE = "recursive";
	static final String CONFIGURABLE = "configurable";
}
