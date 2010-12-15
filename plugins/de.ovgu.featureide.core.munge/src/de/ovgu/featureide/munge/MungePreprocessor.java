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

	private LinkedList<String> selectedFeatures = new LinkedList<String>();
	
	private Configuration configuration;
	
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
		configuration = new Configuration(featureProject.getFeatureModel());
		ConfigurationReader reader = new ConfigurationReader(configuration);
		try {
			reader.readFromFile(equation);
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		
		for (Feature feature : configuration.getSelectedFeatures()) {
			selectedFeatures.add(feature.getName());
		}
		
		//add source files
		try {
			for (IResource res : featureProject.getSourceFolder().members()) {
				if (res instanceof IFolder && selectedFeatures.contains(res.getName())) {
					addDefaultSourceFiles((IFolder)res);
				}
			}
		} catch (CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#clean()
	 */
	public void clean() {
	}

	private void addDefaultSourceFiles(IFolder sourceFolder) throws CoreException {
		ArrayList<String> args = new ArrayList<String>();
		for (Feature feature : configuration.getSelectedFeatures()) {
			args.add("-D" + feature.getName());
		}
		
		boolean filesAdded = false;
		for (IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				addSourceFiles((IFolder)res, featureProject.getBuildFolder().getFolder(res.getName()));
			} else if (res instanceof IFile){
				if (res.getName().endsWith(".java")) {
					args.add(res.getRawLocation().toOSString());
					filesAdded = true;
				}
			}
		}

		if (!filesAdded)
			return;
		
		//add output directory
		args.add(featureProject.getBuildFolder().getRawLocation().toOSString());
		runMunge(args);
	}

	private void addSourceFiles(IFolder sourceFolder, IFolder buildFolder) throws CoreException {
		ArrayList<String> args = new ArrayList<String>();
		for (Feature feature : configuration.getSelectedFeatures()) {
			args.add("-D" + feature.getName());
		}
		createBuildFolder(buildFolder);
		boolean filesAdded = false;
		for (IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				addSourceFiles((IFolder)res, buildFolder.getFolder(res.getName()));
			} else 
			if (res instanceof IFile){
				if (res.getName().endsWith(".java")) {
					args.add(res.getRawLocation().toOSString());
					filesAdded = true;
				}
			}
		}

		if (!filesAdded)
			return;
		
		//add output directory
		args.add(buildFolder.getRawLocation().toOSString());
		runMunge(args);
	}
	
	private void runMunge(ArrayList<String> args) {
		//convert into an Array
		String[] argArray = new String[args.size()];
		for (int i = 0;i < args.size();i++) {
			argArray[i] = args.get(i);
		}
		
		//run Munge
		Munge.main(argArray);
	}

	private void createBuildFolder(IFolder buildFolder) throws CoreException {
		MungeCorePlugin.getDefault().logInfo(buildFolder.getRawLocation().toOSString());
		if (!buildFolder.exists()) {
			buildFolder.create(true, true, null);
		}
		buildFolder.refreshLocal(IResource.DEPTH_ZERO, null);
	}

	@Override
	public boolean copyNotComposedFiles() {
		return false;
	}

	@Override
	public boolean composerSpecficMove(IFolder source, IFolder destination) {
		return false;
	}

	@Override
	public void buildFSTModel() {
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		return null;
	}
}
