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
package de.ovgu.featureide.fm.core;

import java.nio.file.Path;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagator;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.IFileManager;

/**
 * Class that encapsulates any data and method related to FeatureIDE projects.
 * 
 * @author Sebastian Krieter
 */
public class FeatureProject {

	public class FeatureModelChangeListner implements IEventListener {

		public void propertyChange(FeatureIDEEvent evt) {
			final EventType eventType = evt.getEventType();
			switch (eventType) {
			case FEATURE_NAME_CHANGED:
				String oldName = (String) evt.getOldValue();
				String newName = (String) evt.getNewValue();
				FeatureProject.this.renameFeature((IFeatureModel) evt.getSource(), oldName, newName);
				break;
			case MODEL_DATA_LOADED:
				final FeatureProjectStatus status = initStatus();
				for (IFileManager<Configuration> iFileManager : configurationManagerList) {
					iFileManager.setObject(new Configuration(iFileManager.getObject(), status.getFeatureModel()));
				}
			default:
				break;
			}
		}
	}

	public static class FeatureProjectStatus {
		private final FeatureModelFormula formula;
		private final IFeatureModel featureModel;
		private final FeatureModelAnalyzer analyzer;

		private List<Configuration> configurationList = Collections.emptyList();

		public FeatureProjectStatus(FeatureModelFormula formula, IFeatureModel featureModel, FeatureModelAnalyzer analyzer) {
			this.formula = formula;
			this.featureModel = featureModel;
			this.analyzer = analyzer;
		}

		public FeatureModelFormula getFormula() {
			return formula;
		}

		public IFeatureModel getFeatureModel() {
			return featureModel;
		}

		public FeatureModelAnalyzer getAnalyzer() {
			return analyzer;
		}

		public List<Configuration> getConfigurationList() {
			return configurationList;
		}

		public ConfigurationPropagator getPropagator() {
			return getPropagator(new Configuration(featureModel));
		}

		public ConfigurationPropagator getPropagator(Configuration configuration) {
			return new ConfigurationPropagator(formula, configuration);
		}
	}

	private final HashSet<IFileManager<Configuration>> configurationManagerList = new HashSet<>();

	private final IFileManager<IFeatureModel> featureModelManager;

	private FeatureProjectStatus status;

	@Deprecated
	public static ConfigurationPropagator getPropagator(Configuration configuration, boolean includeAbstractFeatures) {
		return new ConfigurationPropagator(configuration, includeAbstractFeatures);
	}

	@Deprecated
	public static ConfigurationPropagator getPropagator(IFeatureModel featureModel, boolean includeAbstractFeatures) {
		final Configuration configuration = new Configuration(featureModel);
		return new ConfigurationPropagator(configuration, includeAbstractFeatures);
	}

	public FeatureProjectStatus getStatus() {
		return status;
	}

	/**
	 * Creating a new ProjectData includes creating folders if they don't exist,
	 * registering workspace listeners and initialization of the wrapper object.
	 * 
	 * @param aProject
	 *            the FeatureIDE project
	 */
	public FeatureProject(IFileManager<IFeatureModel> featureModelManager) {
		// TODO Rename manager method save -> write
		// TODO Implement analyses for configurations

		//TODO synchronize with update method
		this.featureModelManager = featureModelManager;
		featureModelManager.addListener(new FeatureModelChangeListner());

		initStatus();
	}

	private FeatureProjectStatus initStatus() {
		final IFeatureModel featureModel = featureModelManager.getObject();
		final FeatureModelFormula formula = new FeatureModelFormula(featureModel);
		status = new FeatureProjectStatus(formula, featureModel, new FeatureModelAnalyzer(formula, featureModel));
		return status;
	}

	private void renameFeature(final IFeatureModel model, String oldName, String newName) {
		for (IFileManager<Configuration> configurationManager : configurationManagerList) {
			configurationManager.read();
			configurationManager.save();
		}
	}

	public IFileManager<Configuration> getConfigurationManager(String path) {
		IFileManager<Configuration> fileManager = ConfigurationManager.getInstance(new Configuration(featureModelManager.getObject()), path);
		if (fileManager != null && !configurationManagerList.contains(fileManager)) {
			configurationManagerList.add(fileManager);
		}
		return fileManager;
	}

	public void addConfigurationManager(Collection<? extends IFileManager<Configuration>> managerList) {
		configurationManagerList.addAll(managerList);
	}

	public void addConfigurationManager(IFileManager<Configuration> manager) {
		configurationManagerList.add(manager);
	}

	public Path getFeatureModelFile() {
		return featureModelManager.getPath();
	}

	public IFileManager<IFeatureModel> getFeatureModelManager() {
		return featureModelManager;
	}

	public FeatureModelAnalyzer getAnalyzer() {
		final IFeatureModel featureModel = featureModelManager.editObject();
		final FeatureModelFormula formula = new FeatureModelFormula(featureModel);
		return new FeatureModelAnalyzer(formula, featureModel);
	}

	@Override
	public String toString() {
		return featureModelManager.getAbsolutePath();
	}

}
// private IFeatureGraph modalImplicationGraph;
// TODO try to save and load everything
