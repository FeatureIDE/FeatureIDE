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
package de.ovgu.featureide.fm.core.io.xml;

/**
 * Provides the XML tags for {@link XmlFeatureModelReader} and {@link XmlFeatureModelWriter}. 
 * 
 * @author Jens Meinicke
 */
public interface XMLFeatureModelTags {
	static final String FEATURE_MODEL = "featureModel";
	static final String STRUCT = "struct";
	static final String FEATURE_ORDER = "featureOrder";
	static final String COMMENTS = "comments";
	static final String CALCULATIONS = "calculations";
	static final String CONSTRAINTS = "constraints";
	static final String CHOSEN_LAYOUT_ALGORITHM = "chosenLayoutAlgorithm";
	static final String C = "c";
	static final String TRUE = "true";
	static final String FEATURE = "feature";
	static final String OR = "or";
	static final String ALT = "alt";
	static final String AND = "and";
	static final String DESCRIPTION = "description";
	static final String HIDDEN = "hidden";
	static final String USER_DEFINED = "userDefined";
	static final String MANDATORY = "mandatory";
	static final String ABSTRACT = "abstract";
	static final String VAR = "var";
	static final String IMP = "imp";
	static final String EQ = "eq";
	static final String CONJ = "conj";
	static final String DISJ = "disj";
	static final String COORDINATES = "coordinates";
	static final String CALCULATE_FEATURES = "Features";
	static final String CALCULATE_REDUNDANT = "Redundant";
	static final String CALCULATE_TAUTOLOGY = "Tautology";
	static final String CALCULATE_CONSTRAINTS = "Constraints";
	static final String CALCULATE_AUTO = "Auto";
	static final String NAME = "name";
	static final String NOT = "not";
	static final String FALSE = "false";
	static final String SHOW_HIDDEN_FEATURES = "showHiddenFeatures";
	static final String HORIZONTAL_LAYOUT = "horizontalLayout";
	static final String RULE = "rule";
	static final String UNKNOWN = "unknown";
	static final String ATMOST1 = "atmost1";
}
