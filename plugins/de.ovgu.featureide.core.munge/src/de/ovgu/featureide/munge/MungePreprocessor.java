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
package de.ovgu.featureide.munge;

import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;

/**
 * Munge: a purposely-simple Java preprocessor.
 * 
 * @author Jens Meinicke
 */
public class MungePreprocessor implements IComposerExtensionClass{

	private IFeatureProject featureProject = null;
	
	private ArrayList<String> args = new ArrayList<String>();
	private LinkedList<String> selectedFeatures = new LinkedList<String>();
	
	private Boolean sourceFilesAdded;
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#extensions()
	 */
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".java");
		return extensions;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#getEditorID(java.lang.String)
	 */
	public String getEditorID(String extension) {
		if (extension.equals("java"))
			return "org.eclipse.jdt.ui.CompilationUnitEditor";
		return "";
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#initialize(de.ovgu.featureide.core.IFeatureProject)
	 */
	public void initialize(IFeatureProject project) {
		featureProject = project;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#performFullBuild(org.eclipse.core.resources.IFile)
	 */
	public void performFullBuild(IFile equation) {
		assert(featureProject != null) : "Invalid project given";
		
		final String equationPath =  equation.getRawLocation().toOSString();
		final String basePath = featureProject.getSourcePath();
		final String outputPath = featureProject.getBuildPath();
		
		if (equationPath == null || basePath == null || outputPath == null)
			return;
		
		//CommandLine syntax:
		//	–DFEATURE1 –DFEATURE2 ... File1.java File2.java ... outputDirectory
		
		// add symbol definitions
		Configuration configuration = new Configuration(featureProject.getFeatureModel());
		ConfigurationReader reader = new ConfigurationReader(configuration);
		try {
			reader.readFromFile(equation);
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		
		args = new ArrayList<String>();
		for (Feature feature : configuration.getSelectedFeatures()) {
			args.add("-D" + feature.getName());
			selectedFeatures.add(feature.getName());
		}
		
		//add source files
		sourceFilesAdded = false;
		try {
			for (IResource res : featureProject.getSourceFolder().members()) {
				if (res instanceof IFolder && selectedFeatures.contains(res.getName())) {
					addSourceFiles((IFolder)res);
				}
			}
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		if (!sourceFilesAdded)
			return;
		
		//add output directory
		args.add(featureProject.getBuildFolder().getRawLocation().toOSString());
		
		//convert into an Array
		String[] argArray = new String[args.size()];
		for (int i = 0;i < args.size();i++) {
			argArray[i] = args.get(i);
		}
		
		//run Munge
		Munge.main(argArray);
		
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#clean()
	 */
	public void clean() {
	}
	
	private void addSourceFiles(IFolder folder) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				addSourceFiles((IFolder)res);
			} else if (res instanceof IFile){
				if (res.getName().endsWith(".java")) {
					args.add(res.getRawLocation().toOSString());
					sourceFilesAdded = true;
				}
			}
		}
	}
}
