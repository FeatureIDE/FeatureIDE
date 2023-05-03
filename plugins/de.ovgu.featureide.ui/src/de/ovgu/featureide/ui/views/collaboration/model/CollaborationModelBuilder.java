/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.views.collaboration.model;

import static de.ovgu.featureide.fm.core.localization.StringTable.NO_CONFIGURATION;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTConfiguration;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationIO;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * The builder does some modifucations on the FSTModel for presentation at the CollaborationView.
 *
 * @author Constanze Adler
 * @author Jens Meinicke
 * @author Stephan Besecke
 */
public class CollaborationModelBuilder {

	/**
	 * Every feature project has its own filter
	 */
	private final static Map<IFeatureProject, Set<String>> classFilter = new HashMap<>();
	private final static Map<IFeatureProject, Set<String>> featureFilter = new HashMap<>();

	public IFile configuration = null;
	private static FSTModel fSTModel;
	public static IFeatureProject project;

	public static IFile editorFile;

	private static final QualifiedName SHOW_UNSELECTED_FEATURES = new QualifiedName(CollaborationModelBuilder.class.getName() + "#ShowUnselectedFeatures",
			CollaborationModelBuilder.class.getName() + "#ShowUnselectedFeatures");

	private static final String TRUE = "true";
	private static final String FALSE = "false";

	/**
	 * Sets the persistent property of showUnselectedFeatures
	 *
	 * @param value The value to set
	 */
	public static void showUnselectedFeatures(boolean value) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(SHOW_UNSELECTED_FEATURES, value ? TRUE : FALSE);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the the persistent property of <i>showUnselectedFeatures</i>
	 *
	 * @return The persistent property
	 */
	public static final boolean showUnselectedFeatures() {
		try {
			return TRUE.equals(ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(SHOW_UNSELECTED_FEATURES));
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * @return The class filter for the current project
	 */
	public static Set<String> getClassFilter() {
		final Set<String> filter = classFilter.get(project);
		if (filter == null) {
			return new LinkedHashSet<String>();
		}
		return filter;
	}

	/**
	 *
	 * @param filter The class filter for the current project
	 */
	public static void setClassFilter(Set<String> filter) {
		classFilter.put(project, filter);
	}

	/**
	 * @return The feature filter for the current project
	 */
	public static Set<String> getFeatureFilter() {
		final Set<String> filter = featureFilter.get(project);
		if (filter == null) {
			return Collections.emptySet();
		}
		return filter;
	}

	/**
	 *
	 * @param filter The feature filter for the current project
	 */
	public static void setFeatureFilter(Set<String> filter) {
		featureFilter.put(project, filter);
	}

	/**
	 * @param c given class
	 * @return true whether the given class should be diplayed.
	 */
	public static boolean showClass(FSTClass c) {
		if (getClassFilter().isEmpty() || getClassFilter().contains(c.getName())) {
			return showClassForFilteredFeatures(c);
		}
		return false;
	}

	private static boolean showClassForFilteredFeatures(final FSTClass c) {
		if (getFeatureFilter().isEmpty()) {
			if (showUnselectedFeatures()) {
				return true;
			} else {
				for (final FSTRole role : c.getRoles()) {
					if (role.getFeature().isSelected()) {
						return true;
					}
				}
			}
		} else {
			for (final String feature : getFeatureFilter()) {
				for (final FSTRole role : fSTModel.getFeature(feature).getRoles()) {
					if (role.getFSTClass().equals(c)) {
						return true;
					}
				}
			}
		}
		return false;
	}

	/**
	 * @param feature given feature
	 * @return true whether the given feature should be diplayed.
	 */
	public static boolean showFeature(final FSTFeature feature) {
		if (getFeatureFilter().isEmpty()) {
			if (!showFeatureForFilteredClass(feature)) {
				return false;
			}
			if (showUnselectedFeatures()) {
				return true;
			} else {
				return feature.isSelected();
			}
		} else {
			if (getFeatureFilter().contains(feature.getName())) {
				if (!showFeatureForFilteredClass(feature)) {
					return false;
				}
				return true;
			} else {
				return false;
			}
		}
	}

	private static boolean showFeatureForFilteredClass(FSTFeature feature) {
		if (getClassFilter().isEmpty()) {
			return true;
		}

		for (final String classFilter : getClassFilter()) {
			final FSTClass fstClass = fSTModel.getClass(classFilter);
			if (fstClass != null) {
				for (final FSTRole role : fstClass.getRoles()) {
					if (role.getFeature().equals(feature)) {
						return true;
					}
				}
			}
		}

		return false;
	}

	/**
	 * @return <code>true</code> if a filter is defined for the current project.
	 */
	public static boolean isFilterDefined() {
		return !(getClassFilter().isEmpty() && getFeatureFilter().isEmpty());
	}

	public synchronized FSTModel buildCollaborationModel(final IFeatureProject featureProject) {
		if (!initialize(featureProject)) {
			return null;
		}
		return fSTModel;
	}

	private boolean initialize(IFeatureProject featureProject) {
		// set the featureProject
		if (featureProject == null) {
			return false;
		}
		project = featureProject;

		// set the composer
		final IComposerExtensionClass composer = project.getComposer();
		if (composer == null) {
			return false;
		}

		// set the FSTmodel
		getFstModel(composer);

		// add the symbol for the configuration to the model
		if (fSTModel != null) {
			addConfigurationToModel();
		}
		return true;
	}

	/**
	 * sets the FSTModel
	 *
	 * @param composer
	 */
	private void getFstModel(IComposerExtensionClass composer) {
		fSTModel = project.getFSTModel();
		if ((fSTModel == null) || fSTModel.getClasses().isEmpty()) {
			composer.buildFSTModel();
			fSTModel = project.getFSTModel();
		}
	}

	/**
	 * Adds the configuration to the model.
	 */
	private void addConfigurationToModel() {
		final Path config = project.getCurrentConfiguration();
		final FSTConfiguration c;
		if (config == null) {
			c = new FSTConfiguration(NO_CONFIGURATION, configuration, false);
		} else if ((configuration == null) || Objects.equals(EclipseFileSystem.getPath(configuration), config)) {
			c = new FSTConfiguration(FileHandler.getFileName(config) + " ", configuration, true);
		} else {
			c = new FSTConfiguration(FileHandler.getFileName(configuration.getName()) + " ", configuration, false);
		}
		c.setSelectedFeatures(getSelectedFeatures(project));
		fSTModel.setConfiguration(c);
	}

	private Collection<String> getSelectedFeatures(final IFeatureProject featureProject) {
		if (featureProject == null) {
			return Collections.emptySet();
		}

		final Path file = (configuration == null) ? featureProject.getCurrentConfiguration() : EclipseFileSystem.getPath(configuration);

		if ((file == null) || !Files.exists(file)) {
			return Collections.emptySet();
		}

		return readFeaturesfromConfigurationFile(file);
	}

	private Collection<String> readFeaturesfromConfigurationFile(Path file) {
		final Configuration configuration = ConfigurationIO.getInstance().load(file);
		if (configuration != null) {
			return configuration.getSelectedFeatureNames();
		} else {
			return null;
		}
	}
}
