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
package de.ovgu.featureide.core.mpl;

import java.nio.file.Paths;
import java.util.Collection;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.signature.ViewTag;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Holds all relevant information about the interface project.
 *
 * @author Sebastian Krieter
 * @author Reimar Schroeter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class InterfaceProject {

	private final IProject projectReference;
	private final IFeatureProject featureProject;

	private ProjectSignatures projectSignatures = null;

	// private final ViewTagPool viewTagPool = new ViewTagPool();
	// private final AbstractStringProvider stringProvider = new
	// JavaStringProvider();

	private ViewTag filterViewTag = null;
	private int configLimit = 1000;

	private Configuration configuration;

	private final IFeatureModel featureModel;
	private String[] featureNames;

	// private IChainJob loadJob = null;
	// private boolean loadAgain = false;

	public InterfaceProject(IFeatureProject featureProject) {
		this(null, featureProject);
	}

	public InterfaceProject(IProject projectReference) {
		this(projectReference, null);
	}

	private class FeaturePropertyChangeListener implements IEventListener {

		private final int id;

		public FeaturePropertyChangeListener(int id) {
			this.id = id;
		}

		@Override
		public void propertyChange(FeatureIDEEvent event) {
			final EventType prop = event.getEventType();
			if (EventType.LOCATION_CHANGED == prop) {

			} else if (EventType.GROUP_TYPE_CHANGED == prop) {

			} else if (EventType.FEATURE_NAME_CHANGED.equals(prop)) {
				featureNames[id] = ((IFeature) event.getSource()).getName();
			} else if (EventType.ATTRIBUTE_CHANGED.equals(prop)) {

			}
		}
	}

	public InterfaceProject(IProject projectReference, IFeatureProject featureProject) {
		if (projectReference == null) {
			this.projectReference = featureProject.getProject();
		} else {
			this.projectReference = projectReference;
		}
		this.featureProject = featureProject;

		if (projectReference != null) {
			featureModel = FeatureModelManager.load(Paths.get(projectReference.getFile("model.xml").getLocationURI())).getObject();
		} else {
			featureModel = null;
		}
		initFeatureNames();
	}

	private void initFeatureNames() {
		if (featureModel != null) {
			final String[] tempFeatureNames = new String[featureModel.getNumberOfFeatures()];
			int count = 0;

			for (final IFeature feature : featureModel.getFeatures()) {
				if (feature.getStructure().isConcrete()) {
					feature.addListener(new FeaturePropertyChangeListener(count));
					tempFeatureNames[count++] = feature.getName();
				}
			}
			featureNames = new String[count];
			System.arraycopy(tempFeatureNames, 0, featureNames, 0, count);

			// Arrays.sort(featureNames);
			// loadSignatures(true);
		} else {
			featureNames = null;
			projectSignatures = null;
		}
	}

	public int[] getFeatureIDs(Collection<String> featureNames) {
		final int[] ids = new int[featureNames.size()];
		int i = -1;
		for (final String featureName : featureNames) {
			ids[++i] = getFeatureID(featureName);
		}
		return ids;
	}

	public int getFeatureID(String featureName) {
		for (int i = 0; i < featureNames.length; ++i) {
			if (featureNames[i].equals(featureName)) {
				return i;
			}
		}
		return -1;
		// return Arrays.binarySearch(featureNames, featureName);
	}

	public String getFeatureName(int id) {
		return featureNames[id];
	}

	public int getFeatureCount() {
		return featureNames.length;
	}

	// public void loadSignatures(boolean again) {
	// if (loadJob == null) {
	// loadJob = new CreateFujiSignaturesJob();
	// loadJob.setProject(projectReference);
	// JobManager.addJob(projectReference, loadJob);
	// } else if (again) {
	// loadAgain = true;
	// }
	// }

	public ProjectSignatures getProjectSignatures() {
		return projectSignatures;
	}

	public IProject getProjectReference() {
		return projectReference;
	}

	public IFeatureProject getFeatureProjectReference() {
		return featureProject;
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public int getConfigLimit() {
		return configLimit;
	}

	public Configuration getConfiguration() {
		if (configuration == null) {
			final IFile configFile = featureProject.getCurrentConfiguration();
			configuration = new Configuration(featureModel);
			SimpleFileHandler.load(Paths.get(configFile.getLocationURI()), configuration, ConfigFormatManager.getInstance());
		}
		return configuration;
	}

	public ViewTag getFilterViewTag() {
		return filterViewTag;
	}

	// public ViewTagPool getViewTagPool() {
	// return viewTagPool;
	// }

	// public AbstractStringProvider getStringProvider() {
	// return stringProvider;
	// }

	public void setConfiguration(Configuration configuration) {
		this.configuration = configuration;
	}

	public void setProjectSignatures(ProjectSignatures projectSignatures) {
		this.projectSignatures = projectSignatures;
		// loadJob = null;
		// if (loadAgain) {
		// loadSignatures(false);
		// loadAgain = false;
		// }
	}

	public void setConfigLimit(int configLimit) {
		this.configLimit = configLimit;
	}

	public void setFilterViewTag(ViewTag filterViewTag) {
		this.filterViewTag = filterViewTag;
	}

	public void setFilterViewTag(String viewName, int viewLevel) {
		if (viewName != null) {
			filterViewTag = new ViewTag(viewName, viewLevel);
		}
	}

	public void clearFilterViewTag() {
		filterViewTag = null;
	}

	// public void scaleUpViewTag(String name, int level) {
	// viewTagPool.scaleUpViewTags(name, level);
	// }
	//
	// public void removeViewTag(String name) {
	// viewTagPool.removeViewTag(name);
	// }
}
