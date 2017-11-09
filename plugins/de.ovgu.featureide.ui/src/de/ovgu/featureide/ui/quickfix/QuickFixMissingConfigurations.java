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
package de.ovgu.featureide.ui.quickfix;

import static de.ovgu.featureide.fm.core.localization.StringTable.CONFIGURATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_MISSING_CONFIGURATIONS_;

import java.nio.file.Paths;
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
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Default implementation for quick fix of missing configurations.
 *
 * @author Jens Meinicke
 */
public abstract class QuickFixMissingConfigurations implements IMarkerResolution {

	private static final String PREFIX = CONFIGURATION;
	private static final AbstractCorePlugin LOGGER = FMCorePlugin.getDefault();

	protected final IFeatureProject project;
	protected IFeatureModel featureModel;
	private int configurationNr = 0;

	protected final IPersistentFormat<Configuration> configFormat = ConfigurationManager.getDefaultFormat();

	@Override
	public String getLabel() {
		return CREATE_MISSING_CONFIGURATIONS_;
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

	public QuickFixMissingConfigurations(IFeatureModel model) {
		featureModel = model;
		project = null;
	}

	protected IFile getConfigurationFile(final IFolder configFolder) {
		IFile newConfig = null;
		while ((newConfig == null) || newConfig.exists()) {
			newConfig = configFolder.getFile(getConfigurationName(configurationNr));
			configurationNr++;
		}
		return newConfig;
	}

	protected void writeConfigurations(final Collection<Configuration> confs) {
		final FileHandler<Configuration> writer = new FileHandler<>(configFormat);
		try {
			configurationNr = 0;
			for (final Configuration c : confs) {
				final IFile configurationFile = getConfigurationFile(project.getConfigFolder());
				writer.write(Paths.get(configurationFile.getLocationURI()), c);
			}
			project.getConfigFolder().refreshLocal(IResource.DEPTH_ONE, null);
		} catch (final CoreException e) {
			LOGGER.logError(e);
		}
	}

	private String getConfigurationName(final int number) {
		return PREFIX + number + "." + configFormat.getSuffix();
	}

	protected String createShortMessage(Collection<String> features) {
		final StringBuilder message = new StringBuilder();
		int addedFeatures = 0;
		for (final String feature : features) {
			message.append(feature);
			message.append(", ");
			if (addedFeatures++ >= 25) {
				message.append("...");
				break;
			}
		}

		return message.toString();
	}

}
