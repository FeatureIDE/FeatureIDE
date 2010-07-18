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

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Map;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * A general builder used to build every <code>FeatureProject</code>. Using an
 * extension point the real composition algorithm is given, that builds the
 * compiled files.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class ExtensibleFeatureProjectBuilder extends IncrementalProjectBuilder {

	public static final String BUILDER_ID = CorePlugin.PLUGIN_ID
			+ ".extensibleFeatureProjectBuilder";
	public static final String COMPOSER_KEY = "composer";
	
	private IFeatureProject featureProject;
	private IComposerExtension composerExtension;

	private boolean featureProjectLoaded() {
		if (featureProject != null && composerExtension != null)
			return true;

		if (getProject() == null) {
			CorePlugin.getDefault().logWarning("no project got");
			return false;
		}
		featureProject = CorePlugin.getFeatureProject(getProject());
		if (featureProject == null) {
			CorePlugin.getDefault().logWarning("Unable to get feature project");
			return false;
		}

		if ((composerExtension = featureProject.getComposer()) == null) {
			CorePlugin.getDefault().logWarning("No composition tool found");
			featureProject.createBuilderMarker(featureProject.getProject(),
					"Could not load the assigned composition engine: "
							+ featureProject.getComposerID(), 0,
					IMarker.SEVERITY_WARNING);
			return false;
		}

		composerExtension.initialize(featureProject);
		return true;
	}
	
	private boolean cleanBuild = false;
	
	private boolean cleaned = false;
	
	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (!featureProjectLoaded())
			return;
		
		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(),
				IResource.DEPTH_INFINITE);
		
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		
		if(cleanBuild){
			IFile equationFile = featureProject.getCurrentEquationFile();
			if (equationFile == null)
				return;
	
			String equation = equationFile.getName();
			if (equation.contains(".")) {
				equation = equation.substring(0, equation.indexOf('.'));
			}
			if (featureProject.getBuildFolder().getFolder(equation).exists())
				for (IResource res : featureProject.getBuildFolder().getFolder(equation).members())
					res.delete(true, monitor);
			if (featureProject.getBinFolder().getFolder(equation).exists())
				for (IResource res : featureProject.getBinFolder().getFolder(equation).members())
						res.delete(true, monitor);
			
		}else{
			for (IResource member : featureProject.getBinFolder().members())
				member.delete(true, monitor);
			for (IResource member : featureProject.getBuildFolder().members())
				member.delete(true, monitor);
			cleaned = true;
		}	
		
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		cleanBuild = false;
	}

	@SuppressWarnings("rawtypes")
	@Override
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		if (!featureProjectLoaded())
			return null;

		if (!featureProject.buildRelavantChanges() && !cleaned && kind == AUTO_BUILD)
			return null;

		cleaned = false;
		IFile equation = featureProject.getCurrentEquationFile();
		featureProject.deleteBuilderMarkers(getProject(),
				IResource.DEPTH_INFINITE);
		
		try {
			for (IResource res : featureProject.getEquationFolder().members())
				res.refreshLocal(IResource.DEPTH_ZERO, null);
			featureProject.getProject().refreshLocal(IResource.DEPTH_ONE, null);
			cleanBuild = true;
			clean(monitor);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		if (equation == null) {
			return null;
		}
		
		composerExtension.performFullBuild(equation);
		
		featureProject.builded();
		try {
			featureProject.getBuildFolder().refreshLocal(
					IResource.DEPTH_INFINITE, monitor);
			featureProject.getBinFolder().refreshLocal(
					IResource.DEPTH_INFINITE, monitor);
			CorePlugin.getDefault().fireBuildUpdated(featureProject);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		try {
			copy(featureProject.getComposerID(),equation);
		} catch (CoreException e1) {
			CorePlugin.getDefault().logError(e1);
		}
		try {
			featureProject.getBuildFolder().refreshLocal(
					IResource.DEPTH_INFINITE, monitor);
			featureProject.getBinFolder().refreshLocal(
					IResource.DEPTH_INFINITE, monitor);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return null;
		
	}
	// copies all not composed Files from selected Features of src to bin and build
	private void copy(String composerID, IFile equation) throws CoreException{
		String equationName = equation.getName();
		equationName = equationName.substring(0, equationName.indexOf('.'));
			ArrayList<String> selectedFeatures = getSelectedFeatures(equation);
			copyNotComposedFiles(featureProject.getComposer().extensions(), selectedFeatures, equationName);
	}
	
	private void copyNotComposedFiles(ArrayList<String> extensions, ArrayList<String> selectedFeatures, String equationName) throws CoreException{
		boolean binFolderExists = (featureProject.getBinFolder().getFolder(equationName).exists());
		boolean notComposed;
		for (String feature : selectedFeatures)
			for(IResource res : featureProject.getSourceFolder().getFolder(feature).members()){
				notComposed = true;
				for (String extension : extensions)
					if (res.getName().endsWith(extension))
						notComposed = false;
				if (notComposed){
					if (res instanceof IFile){
						res.copy(new Path (featureProject.getBuildFolder().getFolder(equationName).getFullPath().toString()+"/"+res.getName()), true, null);
						if (binFolderExists)
							res.copy(new Path (featureProject.getBinFolder().getFolder(equationName).getFullPath().toString()+"/"+res.getName()), true, null);
					}
					if (res instanceof IFolder){
						createFolder("build/"+equationName+"/"+res.getName());
						if (binFolderExists)
							createFolder("bin/"+equationName+"/"+res.getName());
						for (IResource res2 : ((IFolder) res).members())
							copyNotComposedFiles(extensions, equationName+"/"+res.getName(), res2, binFolderExists);
					}
				}
			}
	}
	
	private void copyNotComposedFiles(ArrayList<String> extensions,String folderName, IResource res, boolean binFolderExists) throws CoreException {
		boolean notComposed = true;
		for (String extension : extensions)
			if (res.getName().endsWith(extension))
				notComposed = false;
		if (notComposed){
			if (res instanceof IFile){
				res.copy(new Path (featureProject.getBuildFolder().getFolder(folderName).getFullPath().toString()+"/"+res.getName()), true, null);
				if (binFolderExists)
					res.copy(new Path (featureProject.getBinFolder().getFolder(folderName).getFullPath().toString()+"/"+res.getName()), true, null);
			}
			if (res instanceof IFolder){
				createFolder("build/"+folderName+"/"+res.getName());
				if (binFolderExists)
					createFolder("bin/"+folderName+"/"+res.getName());
				for (IResource res2 : ((IFolder) res).members())
					copyNotComposedFiles(extensions, folderName+"/"+res.getName(), res2, binFolderExists);
			}
		}
		
	}

	private ArrayList<String> getSelectedFeatures(IFile file) {
		File equation = file.getRawLocation().toFile();
		ArrayList<String> list;
		Scanner scanner = null;

		try {
			scanner = new Scanner(equation);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		if (scanner.hasNext()) {
			list = new ArrayList<String>();
			while (scanner.hasNext()) {
				list.add(scanner.next());
			}
			return list;
		} else {
			return null;
		}
	}
	private void createFolder(String name) {
		IFolder folder = featureProject.getProject().getFolder(name);
		try {
			if (!folder.exists())
				folder.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}
}
