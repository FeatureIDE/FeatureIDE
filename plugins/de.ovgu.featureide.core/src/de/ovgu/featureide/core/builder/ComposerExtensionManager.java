/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.builder;

import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.ExtensionPointManager;


/**
 * Manages the FeatureIDE extensions to compose features.
 * 
 * @author Tom Brosch
 */
public class ComposerExtensionManager extends ExtensionPointManager<IComposerExtension> {

	private static ComposerExtensionManager instance = new ComposerExtensionManager();

	ComposerExtensionManager() {
		super(CorePlugin.PLUGIN_ID, IComposerExtension.extensionPointID);
	}
	
	public static ComposerExtensionManager getInstance() {
		return instance;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.ExtensionPointManager#parseExtension(org.eclipse.core.runtime.IConfigurationElement)
	 */
	@Override
	protected IComposerExtension parseExtension(
			IConfigurationElement configurationElement) {
		if (!configurationElement.getName().equals(IComposerExtension.extensionID))
			return null;
		return new ComposerExtensionProxy(configurationElement);
	}
	
	public List<IComposerExtension> getComposers() {
		return getProviders();
	}
	
	/**
	 * Gets a composer by an I
	 * 
	 * @param composerID The ID of the composer
	 * @return The composer or null if no composer with the specified ID was found
	 */
	public IComposerExtension getComposerById(String composerID) {
		for (IComposerExtension tool : getComposers()) {
			if (tool.getId().equals(composerID))
				return tool;
		}
		return null;
	}
}
