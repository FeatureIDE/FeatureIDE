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
package featureide.core.builder;

import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;

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

	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (!featureProjectLoaded())
			return;
/*
		IFile equationFile = featureProject.getCurrentEquationFile();
		if (equationFile == null)
			return;

		String equation = equationFile.getName();
		if (equation.contains(".")) {
			equation = equation.substring(0, equation.indexOf('.'));
		}
*/
		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(),
				IResource.DEPTH_INFINITE);

		for (IResource member : featureProject.getBinFolder().members())
			member.delete(true, monitor);
		for (IResource member : featureProject.getBuildFolder().members())
			member.delete(true, monitor);
					
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
		featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE,
				monitor);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		if (!featureProjectLoaded())
			return null;

		IFile equation = featureProject.getCurrentEquationFile();

		// TODO #28: implementation for incremental build (delete only builder
		// markers of new builded sources)
		featureProject.deleteBuilderMarkers(getProject(),
				IResource.DEPTH_INFINITE);
		try {
			// TODO #28: replace by change listener, that removes derived
			// resources when their non-derived encounter part is deleted
			clean(monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}

		if (equation == null) {
			// featureProject.createBuilderMarker(getProject(),
			// "No equation file found", 0, IMarker.SEVERITY_WARNING);
			return null;
		}

		composerExtension.performFullBuild(equation);
		/*
		 * if (kind == FULL_BUILD) { //fullBuild(equation);
		 * composer.performFullBuild(equation); } else { IResourceDelta delta =
		 * getDelta(getProject()); if (delta == null) {
		 * composer.performFullBuild(equation); } else { if
		 * (delta.findMember(equation.getProjectRelativePath()) != null) { //
		 * Perform a full build, because the equation file has changed
		 * composer.performFullBuild(equation); } else { //TODO #28: rebuild
		 * classes that reference builded classes //incrementalBuild(delta);
		 * composer.performFullBuild(equation); } } }
		 */

		try {
			featureProject.getBuildFolder().refreshLocal(
					IResource.DEPTH_INFINITE, monitor);
			featureProject.getBinFolder().refreshLocal(
					IResource.DEPTH_INFINITE, monitor);
			CorePlugin.getDefault().fireBuildUpdated(featureProject);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		return null;
	}
}
