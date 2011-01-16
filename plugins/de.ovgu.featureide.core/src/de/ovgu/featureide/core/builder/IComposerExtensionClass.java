/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.core.IFeatureProject;


/**
 * @brief Base interface of all composition tool classes.
 * 
 * Every plugin which extends the de.ovgu.featureide.core.composers needs to provide a class,
 * which implements this interface. Implementing this interface ensures that a given
 * composition tool meets the requirements for composition tools, which are used by the
 * @c ExtensibleFeatureProjectBuilder. This requirements are:
 * - Specifying a path for the composed files (usually "./build")
 * - Specifying a path for the source files (usually "./src")
 * - Specifying a path to the current configuration file (former equation file)
 * - Performing a full build for the current project with a given equation file 
 * 
 * @author Tom Brosch
 */
public interface IComposerExtensionClass {
	
	/**
	 * 
	 * @return a list of file extensions witch can be composed 
	 */
	ArrayList<String> extensions();
	
	/**
	 * 
	 * @param extension
	 * @return ID of the file specific editor for the composer extension
	 */
	String getEditorID(String extension);
	
	void initialize(IFeatureProject project);
	
	void performFullBuild(IFile equation);
	
	/**
	 * 
	 * @return true if project has not to be cleaned anymore
	 */
	boolean clean();
	
	/**
	 * Copys not composed files to the source folder
	 * @return false if not composed files should be moved in a common way
	 */
	boolean copyNotComposedFiles();
	
	/**
	 * Make some changes after adding the FeatureIDE nature
	 * @return true if the source files not have to be moved to the feature folder anymore
	 */
	boolean postAddNature(IFolder source, IFolder destination);
	
	/**
	 * Adds the compiler to the project.
	 */
	void addCompiler(IProject project, String sourcePath, String equationPath, String buildPath);
	
	/**
	 * Creates the FSTModel
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
	 * @return template with replaced markers
	 */
	public String replaceMarker(String text, List<String> list);
	
	/**
	 * This method is called after changes at a file of the buildfolder.
	 * @param buildFile 
	 */
	void postCompile(IFile buildFile);
	
	/**
	 * folders for each feature will be created if true
	 */
	boolean hasFeatureFolders();

	/**
	 * 
	 * @return the index of the default template
	 */
	int getDefaultTemplateIndex();
	
	void postModelChanged();
	
	/**
	 * Text fields at NewFeatureIDProject wizard can be set disabled.  
	 * @param sourcePath
	 * @param equationsPath
	 * @param buildPath
	 */
	void editProjectWizard(Text sourcePath, Text equationsPath, Text buildPath);

}
