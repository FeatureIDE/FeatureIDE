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

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.Platform;

/**
 * Handles extensions via Eclipse framework.
 *
 * @author Sebastian Krieter
 * @author Tom Brosch
 */
public class EclipseExtensionLoader<T extends de.ovgu.featureide.fm.core.IExtension> implements IExtensionLoader<T> {

	protected final Class<T> classObject;
	protected final String pluginID;
	protected final String extensionID;
	protected final String extensionPointID;

	public EclipseExtensionLoader(String pluginID, String extensionPointID, String extensionID, Class<T> classObject) {
		this.pluginID = pluginID;
		this.extensionPointID = extensionPointID;
		this.extensionID = extensionID;
		this.classObject = classObject;
	}

	@Override
	public void loadProviders(ExtensionManager<T> extensionManager) {
		final IExtension[] extensions = Platform.getExtensionRegistry().getExtensionPoint(pluginID, extensionPointID).getExtensions();
		for (final IExtension extension : extensions) {
			final IConfigurationElement[] configurationElements = extension.getConfigurationElements();
			for (final IConfigurationElement configurationElement : configurationElements) {
				final T extensionInstance = parseExtension(configurationElement);
				if (extensionInstance != null) {
					if (extensionInstance.initExtension()) {
						extensionManager.addExtension(extensionInstance);
					}
				}
			}
		}
	}

	protected T parseExtension(IConfigurationElement configurationElement) {
		if (extensionID.equals(configurationElement.getName())) {
			try {
				return classObject.cast(configurationElement.createExecutableExtension("class"));
			} catch (final CoreException e) {
				Logger.logError(e);
			}
		}
		return null;
	}

}
