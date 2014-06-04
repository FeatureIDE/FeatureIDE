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
package de.ovgu.featureide.fm.core;

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
	private IFMComposerExtension fmComposerExtension = new FMComposerExtension();
	private String composerId;

	// TODO duplicate entries
	private final static String COMPOSER_KEY = "composer";
	private final static QualifiedName COMPOSER_CONFIG_ID = new QualifiedName("featureproject.configs", "composer");
	private final static QualifiedName SOURCE_FOLDER_CONFIG_ID = new QualifiedName("featureproject.configs", "source");
	private final static String SOURCE_ARGUMENT = "source";
	private final static String DEFAULT_SOURCE_PATH = "src";
	private final static String BUILDER_ID = "de.ovgu.featureide.core"
			+ ".extensibleFeatureProjectBuilder";
	private IProject project;
	
	/**
	 * 
	 */
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
			if (path != null)
				return path;

			path = getPath(project, SOURCE_ARGUMENT);
			if (path == null)
				return DEFAULT_SOURCE_PATH;
			return path;
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return DEFAULT_SOURCE_PATH;
	}
	
	private String getPath(IProject project, String argument) {
		try {
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (BUILDER_ID.equals(command.getBuilderName())) {
					return command.getArguments().get(argument);
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return null;
	}
	
	private void setComposerID() {
		if(project==null)return;
		try {
			String id = project.getPersistentProperty(COMPOSER_CONFIG_ID);
			if (id != null) {
				composerId = id;
				return;
			}
			
			
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (BUILDER_ID.equals(command.getBuilderName())) {
					id = command.getArguments().get(COMPOSER_KEY);
					if (id != null) {
						composerId = id;
						return;
					}
				}
			}

		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		composerId = null;
	}

	private void setComposer() {
		if (composerId == null) {
			return;
		}
		
		IConfigurationElement[] config = Platform.getExtensionRegistry()
				.getConfigurationElementsFor(
						FMCorePlugin.PLUGIN_ID + ".FMComposer");
		try {
			for (IConfigurationElement e : config) {
				if (e.getAttribute("composer").equals(composerId)) {
					final Object o = e.createExecutableExtension("class");
					if (o instanceof IFMComposerExtension) {
						fmComposerExtension = (IFMComposerExtension) o;
					}
				}
			}
			fmComposerExtension.hasComposer(true);
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	public IFMComposerExtension getFMComposerExtension() {
		return fmComposerExtension;
	}
	
	/**
	 * for unit testing purposes only
	 * @param s
	 */
	public void setComposerID(String s, Object o) {
		composerId = s;
		fmComposerExtension = (IFMComposerExtension)o;
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
	public boolean hasFeaureOrder() {
		return fmComposerExtension.hasFeaureOrder();
	}

	@Override
	public boolean isValidFeatureName(String name) {
		return fmComposerExtension.isValidFeatureName(name);
	}

	@Override
	public String getErroMessage() {
		return fmComposerExtension.getErroMessage();
	}
}
