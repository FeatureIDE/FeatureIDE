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
package de.ovgu.featureide.ui.quickfix;

import java.util.Collection;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IMarkerResolution;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.AbstractCorePlugin;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationWriter;

/**
 * Default implementation for quick fix of missing configurations.
 * 
 * @author Jens Meinicke
 */
public abstract class QuickFixMissingConfigurations implements IMarkerResolution {
	
	private static final String PREFIX = "Configuration";
	private static final AbstractCorePlugin LOGGER = FMCorePlugin.getDefault();
	
	protected final IFeatureProject project;
	protected final FeatureModel featureModel;
	private int configurationNr = 0;
	
	public String getLabel() {
		return "Create missing configurations.";
	}

	public QuickFixMissingConfigurations(final IMarker marker) {
		if (marker != null) {
			project = CorePlugin.getFeatureProject(marker.getResource());
			if (project == null) {
				featureModel = null;
			} else {
				featureModel = project.getFeatureModel();
			}
		} else {
			featureModel = null;
			project = null;
		}
	}

	/**
	 * @param model
	 */
	public QuickFixMissingConfigurations(FeatureModel model) {
		featureModel = model;
		project = null;
	}

	protected void writeConfigurations(final Collection<Configuration> confs) {
		try {
			configurationNr = 0;
			for (final Configuration c : confs) {
				final ConfigurationWriter writer = new ConfigurationWriter(c);
				writer.saveToFile(getConfigurationFile(project.getConfigFolder()));
			}
			project.getConfigFolder().refreshLocal(IResource.DEPTH_ONE, null);
		} catch (CoreException e) {
			LOGGER.logError(e);
		}
	}

	private IFile getConfigurationFile(final IFolder configFolder) {
		IFile newConfig = null;
		while (newConfig == null || newConfig.exists()) {
			newConfig = configFolder.getFile(getConfigurationName(configurationNr));
			configurationNr++;
		}
		return newConfig;
	}
	
	private String getConfigurationName(final int number) {
		return PREFIX + number + "." + project.getComposer().getConfigurationExtension();
	}
	
}
