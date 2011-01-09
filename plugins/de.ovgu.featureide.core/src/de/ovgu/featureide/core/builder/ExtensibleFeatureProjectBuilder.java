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
		
		boolean hasOtherNature = true;
		if (featureProject.getProject().getDescription().getNatureIds().length == 1
				&& featureProject.getProject().hasNature(FeatureProjectNature.NATURE_ID)) {
			hasOtherNature = false;
		}
		
		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(),
				IResource.DEPTH_INFINITE);
		
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		if (!hasOtherNature) {
			featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE,
					monitor);
		}
		
		if(cleanBuild){
			IFile equationFile = featureProject.getCurrentEquationFile();
			if (equationFile == null)
				return;
	
			//String equation = equationFile.getName().split("[.]")[0];
			
			//if (featureProject.getBuildFolder().getFolder(equation).exists())
				for (IResource res : featureProject.getBuildFolder().members()) {//.getFolder(equation).members()) {
						res.delete(true, monitor);
				}
			if (!hasOtherNature) {
				//if (featureProject.getBinFolder().getFolder(equation).exists())
					for (IResource res : featureProject.getBinFolder().members())//.getFolder(equation).members())
							res.delete(true, monitor);
			}
			
		}else{
			if (!hasOtherNature) {
				for (IResource member : featureProject.getBinFolder().members())
					member.delete(true, monitor);
			}
			for (IResource member : featureProject.getBuildFolder().members())
				member.delete(true, monitor);
			cleaned = true;
		}	
		
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		if (!hasOtherNature) {
			featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		}
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
			if (featureProject.getBinFolder() != null) {
				featureProject.getBinFolder().refreshLocal(
						IResource.DEPTH_INFINITE, monitor);
			}
			CorePlugin.getDefault().fireBuildUpdated(featureProject);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		try {
			if (!composerExtension.copyNotComposedFiles()) {
				copy(equation);
			}
		} catch (CoreException e1) {
			CorePlugin.getDefault().logError(e1);
		}
		try {
			featureProject.getBuildFolder().refreshLocal(
					IResource.DEPTH_INFINITE, monitor);
			if (featureProject.getBinFolder() != null)
				featureProject.getBinFolder().refreshLocal(
						IResource.DEPTH_INFINITE, monitor);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return null;
		
	}
	
	// copies all not composed Files of selected Features from src to bin and build
	private void copy(IFile equation) throws CoreException{
		boolean binFolderExists = false;
		if (featureProject.getBinFolder() != null)
			binFolderExists = (featureProject.getBinFolder().exists());
		ArrayList<String > selectedFeatures = getSelectedFeatures(equation);
		if (selectedFeatures != null)
			for (String feature : selectedFeatures)
				if (featureProject.getSourceFolder().getFolder(feature).exists())
					for(IResource res : featureProject.getSourceFolder().getFolder(feature).members())
						copyNotComposedFiles(null, res, binFolderExists);
	}
	
	private void copyNotComposedFiles(String folderName, IResource res, boolean binFolderExists) throws CoreException {
		boolean notComposed = true;
		for (String extension : featureProject.getComposer().extensions())
			if (res.getName().endsWith(extension))
				notComposed = false;
		if (notComposed){
			if (res instanceof IFile){
				if (folderName == null) {
					if (!featureProject.getBuildFolder().getFile(res.getName()).exists())
						res.copy(new Path (featureProject.getBuildFolder().getFullPath().toString()+"/"+res.getName()), true, null);
					if (binFolderExists)
						if (!featureProject.getBuildFolder().getFile(res.getName()).exists())
							res.copy(new Path (featureProject.getBinFolder().getFullPath().toString()+"/"+res.getName()), true, null);
				} else {
					if (!featureProject.getBuildFolder().getFolder(folderName).getFile(res.getName()).exists())
						res.copy(new Path (featureProject.getBuildFolder().getFolder(folderName).getFullPath().toString()+"/"+res.getName()), true, null);
					if (binFolderExists)
						if (!featureProject.getBuildFolder().getFolder(folderName).getFile(res.getName()).exists())
							res.copy(new Path (featureProject.getBinFolder().getFolder(folderName).getFullPath().toString()+"/"+res.getName()), true, null);
				}
			}
			if (res instanceof IFolder){
				if (folderName == null) {
					createFolder(featureProject.getBuildFolder().getName()+"/"+res.getName());
					if (binFolderExists)
						createFolder(featureProject.getBinFolder().getName()+"/"+res.getName());
					for (IResource res2 : ((IFolder) res).members())
						copyNotComposedFiles(res.getName(), res2, binFolderExists);
				} else {
					createFolder(featureProject.getBuildFolder().getName()+"/"+folderName+"/"+res.getName());
					if (binFolderExists)
						createFolder(featureProject.getBinFolder().getName()+"/"+folderName+"/"+res.getName());
					for (IResource res2 : ((IFolder) res).members())
						copyNotComposedFiles(folderName+"/"+res.getName(), res2, binFolderExists);
				}
			}
		}
		
	}


	private static ArrayList<String> getSelectedFeatures(IFile equation) {
		File equationFile = equation.getRawLocation().toFile();
		return getTokenListFromFile(equationFile);
	}

	/**
	 * returns a List of the tokens in file+
	 * this method is public for testing purposes 
	 * 
	 * @param file
	 * @return List of tokens
	 */
	public static ArrayList<String> getTokenListFromFile(File file) {
		ArrayList<String> list = null;
		Scanner scanner = null;

		try {
			scanner = new Scanner(file);

			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}

			}

		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} finally {
			if(scanner!=null)scanner.close();
		}
		return list;
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
