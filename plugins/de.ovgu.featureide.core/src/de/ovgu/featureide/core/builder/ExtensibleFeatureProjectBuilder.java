/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.builder;

import static de.ovgu.featureide.fm.core.localization.StringTable.NO_COMPOSITION_TOOL_FOUND_;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNABLE_TO_GET_PROJECT_;

import java.nio.file.Paths;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * A general builder used to build every <code>FeatureProject</code>. Using an extension point the real composition algorithm is given, that builds the compiled
 * files.
 *
 * @author Tom Brosch
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class ExtensibleFeatureProjectBuilder extends IncrementalProjectBuilder {

	public static final String BUILDER_ID = CorePlugin.PLUGIN_ID + ".extensibleFeatureProjectBuilder";
	public static final String COMPOSER_KEY = "composer";

	private IFeatureProject featureProject;
	private IComposerExtensionClass composerExtension;

	private boolean featureProjectLoaded() {
		if ((featureProject != null) && (composerExtension != null)) {
			return true;
		}

		if (getProject() == null) {
			CorePlugin.getDefault().logWarning(UNABLE_TO_GET_PROJECT_);
			return false;
		}
		featureProject = CorePlugin.getFeatureProject(getProject());
		if (featureProject == null) {

			return false;
		}

		final IStatus status = CorePlugin.getDefault().isComposable(getProject());

		if (!status.isOK() || ((composerExtension = featureProject.getComposer()) == null)) {
			CorePlugin.getDefault().logWarning(NO_COMPOSITION_TOOL_FOUND_);
			featureProject.createBuilderMarker(featureProject.getProject(), status.getMessage(), 0, IMarker.SEVERITY_ERROR);
			return false;
		}
		return true;
	}

	private boolean cleanBuild = false;

	private boolean cleaned = false;

	@Override
	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (!featureProjectLoaded()) {
			return;
		}

		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(), IResource.DEPTH_INFINITE);
		final IProject project = featureProject.getProject();
		if (!composerExtension.clean()) {
			cleaned = false;

			project.refreshLocal(IResource.DEPTH_INFINITE, monitor);
			return;
		}
		boolean hasOtherNature = true;
		if ((project.getDescription().getNatureIds().length == 1) && project.hasNature(FeatureProjectNature.NATURE_ID)) {
			hasOtherNature = false;
		}

		final IFolder buildFolder = featureProject.getBuildFolder();
		final IFolder binFolder = featureProject.getBinFolder();
		final boolean updateBuildeFolder = (buildFolder != null) && buildFolder.isAccessible();
		final boolean updateBinFolder = !hasOtherNature && (binFolder != null) && binFolder.isAccessible();

		if (updateBuildeFolder) {
			buildFolder.refreshLocal(IResource.DEPTH_INFINITE, monitor);
		}
		if (updateBinFolder) {
			binFolder.refreshLocal(IResource.DEPTH_INFINITE, monitor);
		}

		if (cleanBuild) {
			final IFile configFile = featureProject.getCurrentConfiguration();
			if (configFile == null) {
				return;
			}
		} else {
			cleaned = true;
		}

		if (updateBuildeFolder) {
			for (final IResource member : buildFolder.members()) {
				member.delete(true, monitor);
			}
			buildFolder.refreshLocal(IResource.DEPTH_INFINITE, monitor);
		}
		if (updateBinFolder) {
			for (final IResource member : binFolder.members()) {
				member.delete(true, monitor);
			}
			binFolder.refreshLocal(IResource.DEPTH_INFINITE, monitor);
		}
		cleanBuild = false;
	}

	@SuppressWarnings("rawtypes")
	@Override
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		if (!featureProjectLoaded()) {
			return null;
		}

		if (!featureProject.buildRelevantChanges() && !cleaned && (kind == AUTO_BUILD)) {
			return null;
		}

		cleaned = false;
		final IFile configFile = featureProject.getCurrentConfiguration();
		featureProject.deleteBuilderMarkers(getProject(), IResource.DEPTH_INFINITE);

		if (configFile == null) {
			return null;
		}

		try {
			featureProject.getProject().refreshLocal(IResource.DEPTH_ONE, null);
			if (featureProject.getConfigFolder().isAccessible()) {
				featureProject.getConfigFolder().refreshLocal(IResource.DEPTH_ONE, null);
			}
			cleanBuild = true;
			clean(monitor);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

		final IFeatureModel featureModel = featureProject.getFeatureModel();
		if ((featureModel == null) || (featureModel.getStructure().getRoot() == null)) {
			return null;
		}
		composerExtension.performFullBuild(configFile);

		featureProject.built();
		featureProject.checkForProblems();
		try {
			featureProject.getProject().refreshLocal(IResource.DEPTH_INFINITE, monitor);
			CorePlugin.getDefault().fireBuildUpdated(featureProject);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		final Configuration c = new Configuration(featureModel);
		SimpleFileHandler.load(Paths.get(configFile.getLocationURI()), c, ConfigFormatManager.getInstance());
		composerExtension.copyNotComposedFiles(c, null);
		try {
			featureProject.getProject().refreshLocal(IResource.DEPTH_INFINITE, monitor);
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return null;

	}

}
