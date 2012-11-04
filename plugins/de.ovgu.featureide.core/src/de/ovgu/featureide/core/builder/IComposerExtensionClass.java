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
package de.ovgu.featureide.core.builder;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import javax.annotation.Nonnull;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.configuration.Configuration;


/**
 * @brief Base interface of all composition tool classes.
 * 
 * Every plugin which extends the de.ovgu.featureide.core.composers needs to provide a class,
 * which implements this interface. Implementing this interface ensures that a given
 * composition tool meets the requirements for composition tools, which are used by the
 * @c ExtensibleFeatureProjectBuilder. This requirements are:
 * - Specifying a path for the composed files (usually "./build")
 * - Specifying a path for the source files (usually "./src") if hasFeatureFolder()
 * - Specifying a path to the current configuration file
 * - Performing a full build for the current project with a given configuration file 
 * 
 * @author Tom Brosch
 */
public interface IComposerExtensionClass {
	
	final static String PACKAGE_PATTERN = "#package#";
	final static String REFINES_PATTERN = "#refines#";
	final static String CLASS_NAME_PATTERN = "#classname#";
	final static String FEATUE_PATTER = "#featurename#";
		
	boolean initialize(IFeatureProject project);
	
	void performFullBuild(IFile config);
	
	/**
	 * Builds a configuration to the given folder
	 * @param folder The destination
	 * @param configuration The configuration to build
	 * @param congurationName The name of the configuration
	 */
	void buildConfiguration(IFolder folder, Configuration configuration, String congurationName);
	
	/**
	 * 
	 * @return <code>true</code> if clean should be performed before every build
	 */
	boolean clean();
	
	/**
	 * Copies not composed files to the source folder
	 * @param config The configuration file
	 * @param destination The destination to copy
	 */
	void copyNotComposedFiles(IFile config, IFolder destination);
	
	/**
	 * 
	 * @return a list of file extensions witch will be composed 
	 */
	@Nonnull
	LinkedHashSet<String> extensions();
	
	/**
	 * Make some changes after adding the FeatureIDE nature.
	 * @return <code>true</code> if the source files not have to be moved to the feature folder anymore
	 */
	boolean postAddNature(IFolder source, IFolder destination);
	
	/**
	 * Adds the compiler to the project.
	 */
	void addCompiler(IProject project, String sourcePath, String configPath, String buildPath);
	
	/**
	 * Creates the FSTModel without building the project.
	 */
	void buildFSTModel();

	/**
	 * Returns the list of templates for the current composer. <br>
	 * Format: {"File format name", "extension", "template"}
	 * 
	 * @return list of templates for the current composer
	 */
	ArrayList<String[]> getTemplates();
	
	/**
	 * Replaces all markers in the template.
	 * @param text - String, where markers shall be replaced
	 * @param list - List of markers, which depend on user input
	 * @param packageName 
	 * @return template with replaced markers
	 */
	String replaceMarker(String text, List<String> list, String packageName);
	
	/**
	 * Defines if a refining class differs from a common one and <code>replaceMarker()</code>
	 * has to be called.
	 * @return <code>true</code> if the refining class differs.
	 */
	boolean refines();
	
	/**
	 * Is called after changes at composition folder.
	 * @param delta 
	 * @param buildFile 
	 */
	void postCompile(IResourceDelta delta, IFile buildFile);
	
	/**
	 * Folders for each feature will be created if <code>true</code>.
	 */
	boolean hasFeatureFolders();

	/**
	 * 
	 * @return the index of the default template.
	 */
	int getDefaultTemplateIndex();
	
	/**
	 * Is called after changes at the feature model.
	 */
	void postModelChanged();
	
	/**
	 * @return <code>true</code> if the composer has a folder for each features.
	 */
	boolean hasFeatureFolder();

	/**
	 * @return returns <code>false</code> if filenames equal the corresponding feature name
	 * otherwise <code>true</code>.
	 */
	boolean hasCustomFilename();
	
	/**
	 * 
	 * @return the default configuration extension.
	 */
	@Nonnull
	String getConfigurationExtension();

	/**
	 * 
	 * @return <code>false</code> if a source folder should not be created. Default: <code>true</code>
	 */
	boolean hasSourceFolder();

	/** 
	 * @return <code>true</code> if the composition can be called parallel
	 */
	boolean canGeneratInParallelJobs();
	
	/** 
	 * @return <code>true</code> if the fields and Methods can be shown on context Menu of Collaboration Diagram
	 */
	boolean showContextFieldsAndMethods();
	
	/** 
	 * @return List of all FSTDirectives in the text with parent == null
	 * 
	 * @param lines of file / document
	 */
	LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines);
	
	/**
	 * @return <code>true</code> if a highlighting at the editor is available for the composition tool.
	 */
	boolean needColor();
	
	/**
	 * @return <code>true</code> if the composition tool supports contract composition.
	 */
	boolean hasContractComposition();
}
