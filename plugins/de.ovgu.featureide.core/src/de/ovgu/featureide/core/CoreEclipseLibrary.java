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
package de.ovgu.featureide.core;

import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IConfigurationElement;

import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.ComposerExtensionProxy;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.core.internal.ProjectChangeListener;
import de.ovgu.featureide.fm.core.EclipseExtensionLoader;
import de.ovgu.featureide.fm.core.init.ILibrary;

/**
 * The library object for the core plug-in when using the Eclipse platform.
 *
 * @author Sebastian Krieter
 */
public class CoreEclipseLibrary implements ILibrary {

	private IResourceChangeListener listener;

	@Override
	public void install() {
		ComposerExtensionManager.getInstance().addExtensions(new EclipseExtensionLoader<IComposerExtension>(CorePlugin.PLUGIN_ID,
				IComposerExtensionBase.extensionPointID, IComposerExtensionBase.extensionID, IComposerExtension.class) {

			@Override
			protected IComposerExtension parseExtension(IConfigurationElement configurationElement) {
				if (IComposerExtensionBase.extensionID.equals(configurationElement.getName())) {
					try {
						return new ComposerExtensionProxy(configurationElement);
					} catch (final Exception e) {
						CorePlugin.getDefault().logError(e);
					}
				}
				return null;
			}
		});

		listener = new ProjectChangeListener();
		ResourcesPlugin.getWorkspace().addResourceChangeListener(listener);
	}

	@Override
	public void uninstall() {
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(listener);
		listener = null;
	}

}
