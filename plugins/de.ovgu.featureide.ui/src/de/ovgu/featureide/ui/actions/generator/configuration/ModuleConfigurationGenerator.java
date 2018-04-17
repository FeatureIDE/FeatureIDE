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

import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.actions.generator.BuilderConfiguration;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Generates a configuration containing the given feature and a configuration without it.
 *
 * @author Jens Meinicke
 */
public class ModuleConfigurationGenerator extends AConfigurationGenerator {

	private final String featureName;

	public ModuleConfigurationGenerator(ConfigurationBuilder builder, IFeatureModel featureModel, IFeatureProject featureProject, String featureName) {
		super(builder, featureModel, featureProject);
		this.featureName = featureName;
	}

	@Override
	public Void execute(IMonitor monitor) throws Exception {
		buildModule(featureProject, monitor, featureName);
		return null;
	}

	/**
	 * Creates a configuration containing the given feature.
	 *
	 * @param featureProject The feature project
	 * @param featureName The feature to build
	 */
	private void buildModule(IFeatureProject featureProject, IMonitor monitor, String featureName) {
		// create a configuration where the feature is selected
		Configuration configuration = new Configuration(featureModel, true);
		final boolean success = createValidConfiguration(configuration, featureName, Selection.SELECTED);
		if (success) {
			builder.addConfiguration(new BuilderConfiguration(configuration, featureName));
		}

		for (final IFeature coreFeature : featureModel.getAnalyser().getCoreFeatures()) {
			if (coreFeature.getName().equals(featureName)) {
				builder.configurationNumber = 1;
				return;
			}
		}
		// create a configuration without the feature
		configuration = new Configuration(featureModel, true);
		if (configuration.getSelectablefeature(featureName).getAutomatic() != Selection.UNDEFINED) {
			return;
		}
		createValidConfiguration(configuration, featureName, Selection.UNSELECTED);
		if (success) {
			builder.addConfiguration(new BuilderConfiguration(configuration, NOT_ + featureName));
		}
	}

	/**
	 * Selects features to create a valid configuration.
	 *
	 * @param featureName
	 * @param selection
	 */
	private boolean createValidConfiguration(Configuration configuration, String featureName, Selection selection) {
		configuration.setManual(featureName, selection);
		for (final SelectableFeature feature : configuration.getFeatures()) {
			if (feature.getName().equals(featureName)) {
				continue;
			}
			if (configuration.isValid()) {
				break;
			}
			final SelectableFeature selectableFeature = configuration.getSelectablefeature(feature.getName());
			if (selectableFeature.getSelection() == Selection.UNDEFINED) {
				configuration.setManual(selectableFeature, Selection.SELECTED);
			}
		}
		boolean canDeselect = true;
		while (canDeselect) {
			canDeselect = false;
			for (final IFeature feature : configuration.getSelectedFeatures()) {
				if (feature.getName().equals(featureName)) {
					continue;
				}
				final SelectableFeature selectableFeature = configuration.getSelectablefeature(feature.getName());
				try {
					if ((selectableFeature.getAutomatic() == Selection.UNDEFINED) && (selectableFeature.getManual() == Selection.SELECTED)) {
						configuration.setManual(selectableFeature, Selection.UNDEFINED);
						if (!configuration.isValid()) {
							configuration.setManual(selectableFeature, Selection.SELECTED);
						} else {
							canDeselect = true;
						}
					}
				} catch (final Exception e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
		return configuration.isValid();
	}
}
