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
package de.ovgu.featureide.core.builder;

import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;


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
		//	CorePlugin.getDefault().logWarning("Unable to get feature project");
			return false;
		}

		if ((composerExtension = featureProject.getComposer()) == null) {
			CorePlugin.getDefault().logWarning("No composition tool found");
			featureProject.createBuilderMarker(featureProject.getProject(),
					"Could not load the assigned composition engine: "
							+ featureProject.getComposerID(), 0,
					IMarker.SEVERITY_ERROR);
			return false;
		}

		composerExtension.loadComposerExtension();
		return true;
	}
	
	private boolean cleanBuild = false;
	
	private boolean cleaned = false;
	
	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (!featureProjectLoaded())
			return;
		
		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(),
				IResource.DEPTH_INFINITE);
		composerExtension.initialize(featureProject);
		IProject project = featureProject.getProject();
		if (!composerExtension.clean()) {
			cleaned = false;
			
			project.refreshLocal(IResource.DEPTH_INFINITE,
					monitor);
			return;
		}
		boolean hasOtherNature = true;
		if (project.getDescription().getNatureIds().length == 1
				&& project.hasNature(FeatureProjectNature.NATURE_ID)) {
			hasOtherNature = false;
		}

		IFolder buildFolder = featureProject.getBuildFolder();
		if (buildFolder != null) {
			buildFolder.refreshLocal(IResource.DEPTH_INFINITE, monitor);
		}
		IFolder binFolder = featureProject.getBinFolder();
		if (!hasOtherNature) {
			if (binFolder != null && 
					binFolder.exists()) {
				binFolder.refreshLocal(IResource.DEPTH_INFINITE,
						monitor);
			}
		}
		
		if (cleanBuild) {
			IFile configFile = featureProject.getCurrentConfiguration();
			if (configFile == null) {
				return;
			}
		}else{
			cleaned = true;
		}
		if (!hasOtherNature) {
			for (IResource member : binFolder.members())
				member.delete(true, monitor);
		}
		for (IResource member : buildFolder.members()) {
			member.delete(true, monitor);
		}
		
		buildFolder.refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		if (!hasOtherNature) {
			binFolder.refreshLocal(IResource.DEPTH_INFINITE,
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
		IFile configFile = featureProject.getCurrentConfiguration();
		featureProject.deleteBuilderMarkers(getProject(),
				IResource.DEPTH_INFINITE);
		
		try {
			for (IResource res : featureProject.getConfigFolder().members())
				res.refreshLocal(IResource.DEPTH_ZERO, null);
			featureProject.getProject().refreshLocal(IResource.DEPTH_ONE, null);
			cleanBuild = true;
			clean(monitor);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		if (configFile == null) {
			return null;
		}
		FeatureModel featureModel = featureProject.getFeatureModel();
		if(featureModel==null||featureModel.getRoot()==null){
			return null;
		}
		composerExtension.performFullBuild(configFile);
		
		featureProject.built();
		try {
			featureProject.getProject().refreshLocal(IResource.DEPTH_INFINITE, monitor);
			CorePlugin.getDefault().fireBuildUpdated(featureProject);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		Configuration c = new Configuration(featureModel);
		ConfigurationReader reader = new ConfigurationReader(c);
		try {
			reader.readFromFile(configFile);
		} catch (Exception e) {
			CorePlugin.getDefault().logError(e);
		} 
		composerExtension.copyNotComposedFiles(c, featureProject.getBuildFolder());
		try {
			featureProject.getProject().refreshLocal(IResource.DEPTH_INFINITE, monitor);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return null;
		
	}

}
