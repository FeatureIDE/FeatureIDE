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

import java.util.HashMap;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;

/**
 * Manages the composer specific feature models extensions
 *
 * @author Jens Meinicke
 */
public class FMComposerManager implements IFMComposerExtension {

	// TODO duplicate entries
	private final static String COMPOSER_KEY = "composer";
	private final static QualifiedName COMPOSER_CONFIG_ID = new QualifiedName("featureproject.configs", "composer");
	private final static QualifiedName SOURCE_FOLDER_CONFIG_ID = new QualifiedName("featureproject.configs", "source");
	private final static String SOURCE_ARGUMENT = "source";
	private final static String DEFAULT_SOURCE_PATH = "src";
	private final static String BUILDER_ID = "de.ovgu.featureide.core" + ".extensibleFeatureProjectBuilder";
	private final static String MPL_BUILDER_ID = "de.ovgu.featureide.core" + ".mpl.MSPLBuilder";

	private final IProject project;

	private IFMComposerExtension fmComposerExtension = new FMComposerExtension();
	private String composerId;

	public FMComposerManager(IProject project) {
		this.project = project;
		setComposerID();
		setComposer();
	}

	/**
	 * RENAMED to {@link #getProjectSourcePath()}
	 */
	@Deprecated
	String getProjectConfigurationPath() {
		return getProjectSourcePath();
	}

	String getProjectSourcePath() {
		try {
			String path = project.getPersistentProperty(SOURCE_FOLDER_CONFIG_ID);
			if (path != null) {
				return path;
			}

			path = getPath(project, SOURCE_ARGUMENT);
			if (path == null) {
				return DEFAULT_SOURCE_PATH;
			}
			return path;
		} catch (final Exception e) {
			Logger.logError(e);
		}
		return DEFAULT_SOURCE_PATH;
	}

	private void setComposerID() {
		if (project == null) {
			return;
		}
		try {
			String id = project.getPersistentProperty(COMPOSER_CONFIG_ID);
			if (id != null) {
				composerId = id;
				return;
			}

			for (final ICommand command : project.getDescription().getBuildSpec()) {
				if (BUILDER_ID.equals(command.getBuilderName())) {
					id = command.getArguments().get(COMPOSER_KEY);
					if (id != null) {
						composerId = id;
						return;
					}
				}
			}

		} catch (final CoreException e) {
			Logger.logError(e);
		}
		composerId = null;
	}

	private void setComposer() {
		if (composerId == null) {
			return;
		}

		final IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(PluginID.PLUGIN_ID + ".FMComposer");
		try {
			for (final IConfigurationElement e : config) {
				if (e.getAttribute("composer").equals(composerId)) {
					final Object o = e.createExecutableExtension("class");
					if (o instanceof IFMComposerExtension) {
						fmComposerExtension = (IFMComposerExtension) o;
					}
				}
			}
			fmComposerExtension.hasComposer(true);
		} catch (final Exception e) {
			Logger.logError(e);
		}
	}

	public IFMComposerExtension getFMComposerExtension() {
		return fmComposerExtension;
	}

	/**
	 * for unit testing purposes only
	 *
	 * @param s
	 */
	public void setComposerID(String s, Object o) {
		composerId = s;
		fmComposerExtension = (IFMComposerExtension) o;
	}

	// TODO rename method
	@Override
	public void hasComposer(boolean hasComposer) {
		fmComposerExtension.hasComposer(hasComposer);
	}

	@Override
	public String getOrderPageMessage() {
		return fmComposerExtension.getOrderPageMessage();
	}

	@Override
	public boolean performRenaming(String oldName, String newName, IProject project) {
		return fmComposerExtension.performRenaming(oldName, newName, project);
	}

	@Override
	public boolean hasFeatureOrder() {
		return fmComposerExtension.hasFeatureOrder();
	}

	@Override
	public boolean isValidFeatureName(String name) {
		return fmComposerExtension.isValidFeatureName(name);
	}

	@Override
	public String getErrorMessage() {
		return fmComposerExtension.getErrorMessage();
	}

	private static final HashMap<IProject, IFMComposerExtension> map = new HashMap<>();

	public static final IFMComposerExtension getFMComposerExtension(final IProject project) {
		if (project == null) {
			return new FMComposerManager(project);
		}
		IFMComposerExtension extension = map.get(project);
		if (extension == null) {
			extension = new FMComposerManager(project);
			map.put(project, extension);
		}
		return extension;
	}

	public static String getPath(IProject project, String argument) {
		try {
			for (final ICommand command : project.getDescription().getBuildSpec()) {
				if (isFIDEBuilder(command)) {
					return command.getArguments().get(argument);
				}
			}
		} catch (final CoreException e) {
			Logger.logError(e);
		}
		return null;
	}

	public static boolean isFIDEBuilder(ICommand command) {
		final String builderName = command.getBuilderName();
		return BUILDER_ID.equals(builderName) || MPL_BUILDER_ID.equals(builderName);
	}

}
