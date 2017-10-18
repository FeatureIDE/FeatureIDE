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
package de.ovgu.featureide.core.runtime;

import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.jdt.launching.IJavaLaunchConfigurationConstants;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

public class RuntimeLaunchConfigurationDelegate implements ILaunchConfigurationDelegate {

	private final static String COMPOSER_ID = "de.ovgu.featureide.core.composer.runtime";

	@Override
	public void launch(ILaunchConfiguration configuration, final String mode, final ILaunch launch, final IProgressMonitor monitor) throws CoreException {
		final ILaunchConfigurationWorkingCopy launchConfigCopy = configuration.getWorkingCopy();
		IFeatureProject featureProject = null;

		if (launchConfigCopy.getMappedResources().length == 1) {
			featureProject = CorePlugin.getFeatureProject(launchConfigCopy.getMappedResources()[0]);
		}

		if ((featureProject != null) && featureProject.getComposerID().equals(COMPOSER_ID)
			&& RuntimeParameters.RUN_CONFIGURATION.equals(featureProject.getCompositionMechanism())) {

			final Configuration featureProjectConfig = new Configuration(featureProject.getFeatureModel());

			final String userDefinedArgs = launchConfigCopy.getAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, "");

			final Path configPath = Paths.get(featureProject.getCurrentConfiguration().getLocationURI());
			SimpleFileHandler.load(configPath, featureProjectConfig, ConfigFormatManager.getInstance());

			String args = userDefinedArgs;
			for (final SelectableFeature f : featureProjectConfig.getFeatures()) {
				if (!f.getFeature().getStructure().isAbstract()) {
					if (f.getSelection() == Selection.SELECTED) {
						args += " " + f.getFeature().getName();
						launchConfigCopy.setAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, args);
					}
				}
			}

			new org.eclipse.jdt.launching.JavaLaunchDelegate().launch(launchConfigCopy, mode, launch, monitor);

			launchConfigCopy.setAttribute(IJavaLaunchConfigurationConstants.ATTR_PROGRAM_ARGUMENTS, userDefinedArgs);
			configuration = launchConfigCopy.doSave();

		} else {
			new org.eclipse.jdt.launching.JavaLaunchDelegate().launch(launchConfigCopy, mode, launch, monitor);
		}
	}
}
