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
package de.ovgu.featureide.ui.actions.generator.configuration;

import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor.MethodCancelException;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.actions.generator.BuilderConfiguration;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Generates all current configurations in the config folder.
 *
 * @author Jens Meinicke
 */
public class CurrentConfigurationsGenerator extends AConfigurationGenerator {

	public CurrentConfigurationsGenerator(ConfigurationBuilder builder, IFeatureModel featureModel, IFeatureProject featureProject) {
		super(builder, featureModel, featureProject);
		builder.configurationNumber = Math.min(builder.configurationNumber, countConfigurations(featureProject.getConfigFolder()));
	}

	@Override
	public Void execute(IMonitor monitor) throws Exception {
		buildCurrentConfigurations(builder.featureProject, monitor);
		return null;
	}

	protected void buildCurrentConfigurations(IFeatureProject featureProject, IMonitor monitor) {
		try {
			for (final IResource configuration : featureProject.getConfigFolder().members()) {
				if (confs >= maxConfigs()) {
					break;
				}
				try {
					monitor.checkCancel();
				} catch (final MethodCancelException e) {
					builder.finish();
					return;
				}
				if (isConfiguration(configuration)) {
					build(configuration, monitor);
					confs++;
				}
			}
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Builds the given configuration file into the folder for current configurations.
	 *
	 * @param configuration The configuration file
	 * @param monitor
	 */
	private void build(IResource configuration, IMonitor monitor) {
		SimpleFileHandler.load(Paths.get(configuration.getLocationURI()), this.configuration, ConfigFormatManager.getInstance());
		builder.addConfiguration(new BuilderConfiguration(this.configuration, configuration.getName().split("[.]")[0]));
	}

	/**
	 * @param res A file.
	 * @return <code>true</code> if the given file is a configuration file
	 */
	private boolean isConfiguration(IResource res) {
		return (res instanceof IFile) && ConfigFormatManager.getInstance().hasFormat(res.getName());
	}

	/**
	 * Counts the configurations at the given folder.
	 *
	 * @param configFolder The folder
	 * @return Number of configuration files
	 */
	private int countConfigurations(IFolder configFolder) {
		int i = 0;
		try {
			for (final IResource res : configFolder.members()) {
				if (isConfiguration(res)) {
					i++;
				}
			}
		} catch (final CoreException e) {
			UIPlugin.getDefault().logError(e);
		}
		return i;
	}

}
