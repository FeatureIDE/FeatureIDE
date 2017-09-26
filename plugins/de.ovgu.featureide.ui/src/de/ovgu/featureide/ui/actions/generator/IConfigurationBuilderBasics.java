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
package de.ovgu.featureide.ui.actions.generator;

import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_ALL_CURRENT_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_ALL_VALID_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_INTEGRATION_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.COUNT_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.HAS_BEEN_DEPRECATED;
import static de.ovgu.featureide.fm.core.localization.StringTable.PRODUCTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.REDUNDANT_CAST_TO;
import static de.ovgu.featureide.fm.core.localization.StringTable.SERIALIZABLE_CLASS;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_IMPORT;
import static de.ovgu.featureide.fm.core.localization.StringTable.VARIANT;

import java.util.regex.Pattern;

import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.core.CorePlugin;

/**
 * Defining static fields for the ConfigurationBuilder
 *
 * @see ConfigurationBuilder
 * @see BuildAllCurrentConfigurationsAction
 * @see BuildAllValidConfigurationsAction
 * @see BuildProductsAction
 *
 * @author Jens Meinicke
 */
public interface IConfigurationBuilderBasics {

	enum BuildType {
		ALL_VALID, ALL_CURRENT, T_WISE, INTEGRATION, RANDOM
	};

	enum BuildOrder {
		DEFAULT, DISSIMILARITY, INTERACTION
	};

	enum TWise {
		ICPL, CHVATAL, CASA, INCLING
	}

	/** Saves the toggle state whether new projects should be generated for each configuration. **/
	QualifiedName TOGGLE_STATE =
		new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#CreateNewProject", IConfigurationBuilderBasics.class.getName() + "#CreateNewProject");
	QualifiedName T_WISE = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#T-Wise", IConfigurationBuilderBasics.class.getName() + "#T-Wise");
	QualifiedName T_INTERACTION =
		new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#T-Order", IConfigurationBuilderBasics.class.getName() + "#T-Order");
	QualifiedName GENERATE =
		new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#Generate", IConfigurationBuilderBasics.class.getName() + "#Generate");
	QualifiedName ORDER = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#Order", IConfigurationBuilderBasics.class.getName() + "#Order");
	QualifiedName TEST = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#Test", IConfigurationBuilderBasics.class.getName() + "#Test");
	QualifiedName MAX = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#MaxConf", IConfigurationBuilderBasics.class.getName() + "#MaxConf");
	String TRUE = "true";
	String FALSE = "false";

//------------------------------------------------------------------------------

	/**
	 * Basics for the ConfigurationBuilder.
	 */
	String JOB_TITLE = BUILD_ALL_VALID_CONFIGURATIONS;
	String JOB_TITLE_CURRENT = BUILD_ALL_CURRENT_CONFIGURATIONS;
	String JOB_TITLE_T_WISE = "Build t-wise configurations";
	String JOB_TITLE_RANDOM = "Build random configurations";
	String JOB_TITLE_MODULE = BUILD_INTEGRATION_CONFIGURATIONS;

	String JOB_TITLE_COUNT_CONFIGURATIONS = COUNT_CONFIGURATIONS;

	String CONFIGURATION_NAME = VARIANT;
	String FOLDER_NAME = PRODUCTS;
	String FOLDER_NAME_CURRENT = "currentproducts";
	String TEMPORARY_BIN_FOLDER = ".tmpBin";

	String PROBLEM_MARKER = CorePlugin.PLUGIN_ID + ".variantMarker";
	String ERROR_IGNOR_RAW_TYPE = "raw type";
	String ERROR_IGNOR_SERIIZABLE = SERIALIZABLE_CLASS;
	String ERROR_IGNOR_CAST = REDUNDANT_CAST_TO;
	String ERROR_IGNOR_DEPRECATION = HAS_BEEN_DEPRECATED;
	String ERROR_IGNOR_UNUSED_IMPORT = THE_IMPORT;

	Pattern errorMessagePattern = Pattern.compile("(.+):(\\d+):(.+)");

	String SEPARATOR_VARIANT = "_v.";
	String SEPARATOR_CONFIGURATION = "_c.";
	String SEPARATOR_T_WISE = "_t.";
	String SEPARATOR_RANDOM = "_r.";
	String SEPARATOR_INTEGRATION = "_i.";

	/**
	 * Basics for the SPLCATool.
	 */
	int CHVATAL_MAX = 4;
	int ICPL_MAX = 3;
	int CASA_MAX = 6;
	int MASK_MAX = 2;
}
