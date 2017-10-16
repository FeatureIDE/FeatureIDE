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
package de.ovgu.featureide.fm.ui;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;
import org.eclipse.swt.graphics.Image;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.io.ExternalChangeListener;
import de.ovgu.featureide.fm.ui.editors.EclipseExternalChangeListener;

/**
 * The activator class controls the plug-in life cycle.
 *
 * @author Christian Kaestner
 * @author Thomas Thuem
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public class FMUIPlugin extends AbstractUIPlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.ui";

	private static FMUIPlugin plugin;

	protected boolean isOnlyFeatureModelingInstalled;

	IResource projectResource;
	ConfigurationWizard extension;

	@Override
	public String getID() {
		return PLUGIN_ID;
	}

	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		final EclipseExternalChangeListener eclipseExternalChangeListener = new EclipseExternalChangeListener();
		ExternalChangeListener.listener = eclipseExternalChangeListener;
		ResourcesPlugin.getWorkspace().addResourceChangeListener(eclipseExternalChangeListener);
		isOnlyFeatureModelingInstalled = this.checkExistenceOfExtension("de.ovgu.featureide.fm.ui.ConfigurationWizard");
	}

	@Override
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
		final ExternalChangeListener listener = ExternalChangeListener.listener;
		if (listener instanceof IResourceChangeListener) {
			ResourcesPlugin.getWorkspace().removeResourceChangeListener((IResourceChangeListener) listener);
		}
	}

	public static FMUIPlugin getDefault() {
		return plugin;
	}

	public static Image getImage(String name) {
		return getDefault().getImageDescriptor("icons/" + name).createImage();
	}

	/**
	 * @return the isOnlyFeatureModelingInstalled
	 */
	public boolean isOnlyFeatureModelingInstalled() {
		return isOnlyFeatureModelingInstalled;
	}

	public boolean setProjectResource(IResource res, IPath chosenPath) {
		projectResource = res;
		return extension.setWarningMessage(res, chosenPath);
	}

	public String getExtensionWarningMessage() {
		return extension.getMessage();
	}

	/**
	 * If there is no extension (core plugin project is closed, or not installed) then this means, that the user has chosen to only install or use FeatureIDE
	 * with only "Feature Modeling" installed, under this circumstances there is no possibility to use the "New FeatureIDE Project" wizard and other features
	 * which are provided by the not installed plugins.
	 *
	 * 
	 * @param extensionPointId
	 * @return true if only feature modeling is installed, false if the extension of the core plugin exists (i.e. everything is installed, or at least the core
	 *         plugin)
	 * @throws CoreException
	 */
	protected boolean checkExistenceOfExtension(String extensionPointId) throws CoreException {
		IExtensionRegistry reg = Platform.getExtensionRegistry();
		IExtensionPoint ep = reg.getExtensionPoint(extensionPointId);
		org.eclipse.core.runtime.IExtension[] extensions = ep.getExtensions();

		if (1 == extensions.length) {
			IConfigurationElement[] ce = extensions[0].getConfigurationElements();
			for (int i = 0; i < ce.length; i++) {
				Object obj = ce[i].createExecutableExtension("class");
				if (obj instanceof ConfigurationWizard) {
					//save the reference for later use
					extension = ((ConfigurationWizard) obj);
				}
			}
			return false;
		} else {
			// Core plugin is not available, FeatureIDE project wizard will not show up
			return true;
		}
	}

}
