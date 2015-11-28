/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collection;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.ui.IMarkerResolution;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Default implementation for quick fix of missing configurations.
 * 
 * @author Jens Meinicke
 */
public abstract class QuickFixMissingConfigurations implements IMarkerResolution {

	private static final String PREFIX = CONFIGURATION;

	protected final IFeatureProject project;
	protected FeatureModel featureModel;
	private int configurationNr = 0;

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

	public QuickFixMissingConfigurations(FeatureModel model) {
		featureModel = model;
		project = null;
	}

	protected IFile getConfigurationFile(final IFolder configFolder) {
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

	protected String createShortMessage(Collection<String> features) {
		StringBuilder message = new StringBuilder();
		int addedFeatures = 0;
		for (String feature : features) {
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
