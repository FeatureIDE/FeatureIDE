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
package de.ovgu.featureide.ui.statistics.core;

import static de.ovgu.featureide.fm.core.localization.StringTable.ATOMIC_SETS_OF_THE_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE___DETAILS;
import static de.ovgu.featureide.fm.core.localization.StringTable.GENERATION_TOOL;
import static de.ovgu.featureide.fm.core.localization.StringTable.LINES_OF_CODE;
import static de.ovgu.featureide.fm.core.localization.StringTable.METHOD_CONTRACTS_IN_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.METHOD_CONTRACT_REFINEMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_ABSTRACT_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_CLASSES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_CLASSES_WITH_CLASS_INVARIANTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_CLASSES_WITH_METHOD_CONTRACTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_CLASS_INVARIANTS_IN_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_COMPOUND_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_CONCRETE_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_FEATURES_IN_CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_FIELDS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_HIDDEN_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_METHODS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_METHODS_WITH_METHOD_CONTRACTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_METHOD_CONTRACTS_IN_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_NESTED_CLASSES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_PROGRAM_VARIANTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_ROLES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_TERMINAL_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_UNIQUE_FIELDS;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_UNIQUE_METHODS;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_OPEN_A_FEATURE_DIAGRAM_EDITOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.RELATIVE_NUMBER_OF_FEATURES_IN_CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SEMANTICAL_STATISTICS_OF_THE_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.STATISTICS_OF_PRODUCT_LINE_IMPLEMENTATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.STATISTICS_OF_PRODUCT_LINE_SPECIFICATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.SYNTACTICAL_STATISTICS_OF_THE_FEATURE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.TIMEOUT_STRING;

import java.util.HashMap;

import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Defines descriptions for nodes in the TreeViewer in order to keep everything in one place.
 *
 * @see Parent
 * @see TreeViewer
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public interface StatisticsIds {

	public static final String OPEN_FILE = PLEASE_OPEN_A_FEATURE_DIAGRAM_EDITOR;
	public static final String PRODUCT_LINE_IMPLEMENTATION = STATISTICS_OF_PRODUCT_LINE_IMPLEMENTATION;
	public static final String CONTRACT_COMPLEXITY = STATISTICS_OF_PRODUCT_LINE_SPECIFICATION;
	public static final String SEMANTICAL_STATISTICS = SEMANTICAL_STATISTICS_OF_THE_FEATURE_MODEL;
	public static final String ATOMIC_SETS = ATOMIC_SETS_OF_THE_FEATURE_MODEL;
	public static final String CORE_FEATURES = "Number of core features";
	public static final String DEAD_FEATURES = "Number of dead features";
	public static final String FO_FEATURES = "Number of false-optional features";
	public static final String SYNTACTICAL_STATISTICS = SYNTACTICAL_STATISTICS_OF_THE_FEATURE_MODEL;
	public static final String SEPARATOR = ": ";
	public static final String CLASS_SEPARATOR = "$";
	public static final String NUMBER_FEATURES = NUMBER_OF_FEATURES;
	public static final String NUMBER_CONCRETE = NUMBER_OF_CONCRETE_FEATURES;
	public static final String NUMBER_ABSTRACT = NUMBER_OF_ABSTRACT_FEATURES;
	public static final String NUMBER_TERMINAL = NUMBER_OF_TERMINAL_FEATURES;
	public static final String NUMBER_COMPOUND = NUMBER_OF_COMPOUND_FEATURES;
	public static final String NUMBER_HIDDEN = NUMBER_OF_HIDDEN_FEATURES;
	public static final String NUMBER_CONSTRAINTS = NUMBER_OF_CONSTRAINTS;
	public static final String NUMBER_CONSTRAINT_FEATURES = NUMBER_OF_FEATURES_IN_CONSTRAINTS;
	public static final String CONSTRAINT_RATIO = RELATIVE_NUMBER_OF_FEATURES_IN_CONSTRAINTS;
	public static final String MODEL_VOID = "Feature model is valid (not void)";
	public static final String MODEL_TIMEOUT = MODEL_VOID + TIMEOUT_STRING;
	public static final String DESC_COMPOSER_NAME = GENERATION_TOOL;
	public static final String DESC_CONFIGS = NUMBER_OF_CONFIGURATIONS;
	public static final String DESC_VARIANTS = NUMBER_OF_PROGRAM_VARIANTS;
	public static final String DESC_FEATURE_COMPLEXITY = FEATURE___DETAILS;
	public static final String NUMBER_ROLE = NUMBER_OF_ROLES;
	public static final String NUMBER_CLASS = NUMBER_OF_CLASSES;
	public static final String NUMBER_CLASS_NESTED = NUMBER_OF_NESTED_CLASSES;
	public static final String NUMBER_METHOD = NUMBER_OF_METHODS;
	public static final String NUMBER_FIELD = NUMBER_OF_FIELDS;
	public static final String NUMBER_METHOD_U = NUMBER_OF_UNIQUE_METHODS;
	public static final String NUMBER_FIELD_U = NUMBER_OF_UNIQUE_FIELDS;
	public static final String NUMBER_OF_CODELINES = LINES_OF_CODE;

	public static final String NUMBER_PROJECT_METHOD_CONTRACT = NUMBER_OF_METHOD_CONTRACTS_IN_PROJECT;
	public static final String NUMBER_PROJECT_INVARIANT = NUMBER_OF_CLASS_INVARIANTS_IN_PROJECT;
	public static final String NUMBER_CLASS_METHOD_CONTRACT = NUMBER_OF_CLASSES_WITH_METHOD_CONTRACTS;
	public static final String NUMBER_CLASS_INVARIANT = NUMBER_OF_CLASSES_WITH_CLASS_INVARIANTS;
	public static final String NUMBER_METHOD_METHOD_CONTRACT = NUMBER_OF_METHODS_WITH_METHOD_CONTRACTS;
	public static final String METHOD_CONTRACT_REFINEMENT = METHOD_CONTRACT_REFINEMENTS;
	public static final String METHOD_CONTRACTS_FEATURE = METHOD_CONTRACTS_IN_FEATURES;

	public static final HashMap<String, String> REFINEMENT_COMPOSING_MECHANISM_MAPPING = new HashMap<String, String>() {

		private static final long serialVersionUID = 1L;

		{
			put("", "No keyword");
			put("\\final_contract", "Plain Contracting");
			put("\\consecutive_contract", "Consecutive Contract");
			put("\\conjunctive_contract", "Conjunctive Contract");
			put("\\cumulative_contract", "Cumulative Contract");
			put("\\final_method", "Final Method");
		}
	};

}
