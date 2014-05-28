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
package de.ovgu.featureide.ui.actions.generator;

import java.util.regex.Pattern;

import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.core.CorePlugin;

/**
 * Defining static fields for the ConfigurationBuilder
 * @see ConfigurationBuilder
 * @see BuildAllCurrentConfigurationsAction
 * @see BuildAllValidConfigurationsAction 
 * @see BuildProductsAction
 * 
 * @author Jens Meinicke
 */
public interface IConfigurationBuilderBasics {
	
	enum BuildType {ALL_VALID, ALL_CURRENT, T_WISE};
	enum BuildOrder {DEFAULT, DIFFERENCE, INTERACTION};
	enum TWise {ICPL, CHVATAL, CASA}
	
	/**
	 * Basics for the dialogs.
	 */
	String MESSAGE_TITLE_VALID = "Build all valid configurations";
	String MESSAGE_TITLE_CURRENT = "Build all current configurations";
	String MESSAGE_TITLE_T = "Build T-Wise configurations";
	String MESSAGE_CURRENT = "Builds all current configurations";
	String MESSAGE_START = "Build all valid program variants.";
	String TOGGLE_MESSAGE = "Create a new project for each variant";
	
	/** Saves the toggle state whether new projects should be generated for each configuration. **/
	QualifiedName TOGGLE_STATE = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#CreateNewProject", 
			IConfigurationBuilderBasics.class.getName() + "#CreateNewProject");
	QualifiedName T_WISE = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#T-Wise", 
			IConfigurationBuilderBasics.class.getName() + "#T-Wise");
	QualifiedName GENERATE = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#Generate", 
			IConfigurationBuilderBasics.class.getName() + "#Generate");
	QualifiedName ORDER = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#Order", 
			IConfigurationBuilderBasics.class.getName() + "#Order");
	QualifiedName BUFFER = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#Buffer", 
			IConfigurationBuilderBasics.class.getName() + "#Buffer");
	String TRUE = "true";
	String FALSE = "false";
	
//------------------------------------------------------------------------------
	
	/**
	 * Basics for the ConfigurationBuilder.
	 */
	String JOB_TITLE = "Build all valid configurations";
	String JOB_TITLE_CURRENT = "Build all current configurations";
	String JOB_TITLE_T_WISE = "Build t-wise configurations";
	
	String JOB_TITLE_COUNT_CONFIGURATIONS = "Count configurations";
	
	String CONFIGURATION_NAME = "Variant";
	String FOLDER_NAME = "products";
	String FOLDER_NAME_CURRENT = "currentproducts";
	String TEMPORARY_BIN_FOLDER = ".tmpBin";
	
	String PROBLEM_MARKER = CorePlugin.PLUGIN_ID + ".variantMarker";
	String CANNOT_FIND_SYMBOL = "cannot find symbol";
	String ERROR_IGNOR_RAW_TYPE = "raw type";
	String ERROR_IGNOR_SERIIZABLE = "serializable class";
	String ERROR_IGNOR_CAST = "redundant cast to";
	String ERROR_IGNOR_DEPRECATION = "has been deprecated";
	
	Pattern errorMessagePattern = Pattern.compile("(.+):(\\d+):(.+)");
	
	String SEPARATOR_VARIANT = "_v.";
	String SEPARATOR_CONFIGURATION = "_c.";
	String SEPARATOR_T_WISE = "_t.";
	
	String T_WISE_CONFIGURATIONS = "T-Wise configurations";
	String ALL_CURRENT_CONFIGURATIONS = "All current configurations";
	String ALL_VALID_CONFIGURATIONS = "All valid configurations";
	
	String INTERACTIONS = "Interactions";
	String DIFFERENCE = "Difference";
	String DEFAULT = "Default";
	
	/**
	 * Basics for the SPLCATool.
	 */
	int CHVATAL_MAX = 4;
	int ICPL_MAX = 3;
	int CASA_MAX = 6;
	String CHVATAL = "Chvatal"; 
	String ICPL = "ICPL (fastest)";
	String CASA = "CASA";
}
