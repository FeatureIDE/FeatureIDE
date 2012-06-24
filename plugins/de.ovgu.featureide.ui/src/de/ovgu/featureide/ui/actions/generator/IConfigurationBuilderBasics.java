/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.ui.actions.generator;

import java.util.regex.Pattern;

import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.core.CorePlugin;

/**
 * Defining static fields for the ConfigurationBuilder
 * @see ConfigurationBuilder
 * @see BuildAllConfigurationsAction
 * @see BuildAllValidConfigurationsAction 
 * 
 * @author Jens Meinicke
 */
public interface IConfigurationBuilderBasics {
	
	/**
	 * Basics for the dialogs.
	 */
	final static String MESSAGE_TITLE_VALID = "Build all valid configurations";
	final static String MESSAGE_TITLE_CURRENT = "Build all current configurations";
	final static String MESSAGE_CURRENT = "Builds all current configurations";
	final static String MESSAGE_START = "This could take a long time.\nThe current algorithm is inefficient, if your model contains many constraints.\n";
	final static String TOGGLE_MESSAGE = "Create a new project for each variant";
	
	static final QualifiedName TOGGLE_STATE = new QualifiedName(IConfigurationBuilderBasics.class.getName() + "#CreateNewProject", 
			IConfigurationBuilderBasics.class.getName() + "#CreateNewProject");
	final static String TRUE = "true";
	final static String FALSE = "false";
	
//------------------------------------------------------------------------------
	
	/**
	 * Basics for the ConfigurationBuilder.
	 */
	final static String JOB_TITLE = "Build all valid configurations";
	final static String JOB_TITLE_CURRENT = "Build all current configurations";
	final static String JOB_TITLE_COUNT_CONFIGURATIONS = "Count configurations";
		
	final static String CONFIGURATION_NAME = "Variant";
	final static String FOLDER_NAME = "products";
	final static String FOLDER_NAME_CURRENT = "currentproducts";
	final static String TEMPORARY_BIN_FOLDER = ".tmpBin";
	
	final static String PROBLEM_MARKER = CorePlugin.PLUGIN_ID + ".variantMarker";
	final static String CANNOT_FIND_SYMBOL = "cannot find symbol";
	final static String ERROR_IGNOR_RAW_TYPE = "raw type";
	final static String ERROR_IGNOR_SERIIZABLE = "serializable class";
	final static String ERROR_IGNOR_CAST = "redundant cast to";
	final static String ERROR_IGNOR_DEPRECATION = "has been deprecated";
	
	final static Pattern errorMessagePattern = Pattern.compile("(.+):(\\d+):(.+)");
	
	final static String SEPARATOR_VARIANT = " v.";
	final static String SEPARATOR_CONFIGURATION = " c.";
}
