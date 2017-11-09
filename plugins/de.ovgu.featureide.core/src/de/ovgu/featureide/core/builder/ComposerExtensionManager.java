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
package de.ovgu.featureide.core.builder;

import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_AVAILABLE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_REQUIRED_COMPOSER;

import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.EclipseExtensionLoader;
import de.ovgu.featureide.fm.core.ExtensionManager;
import de.ovgu.featureide.fm.core.Logger;

/**
 * Manages the FeatureIDE extensions to compose features.
 *
 * @author Tom Brosch
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
public class ComposerExtensionManager extends ExtensionManager<IComposerExtension> {

	private static ComposerExtensionManager instance = new ComposerExtensionManager();

	private ComposerExtensionManager() {
		setExtensionLoaderInternal(new EclipseExtensionLoader<IComposerExtension>(CorePlugin.PLUGIN_ID, IComposerExtensionBase.extensionPointID,
				IComposerExtensionBase.extensionID, IComposerExtension.class) {

			@Override
			protected IComposerExtension parseExtension(IConfigurationElement configurationElement) {
				if (IComposerExtensionBase.extensionID.equals(configurationElement.getName())) {
					try {
						return new ComposerExtensionProxy(configurationElement);
					} catch (final Exception e) {
						Logger.logError(e);
					}
				}
				return null;
			}
		});
	}

	public static ComposerExtensionManager getInstance() {
		return instance;
	}

	public List<IComposerExtension> getComposers() {
		return getExtensions();
	}

	/**
	 * Gets a composer by an ID
	 *
	 * @param composerID The ID of the composer
	 * @return The composer or null if no composer with the specified ID was found
	 */
	public IComposerExtensionClass getComposerById(IFeatureProject featureProject, String composerID) {
		for (final IComposerExtension tool : getComposers()) {
			if (tool.getId().equals(composerID)) {
				return tool.getComposerByProject(featureProject);
			}
		}
		return null;
	}

	public IComposerExtension getComposerById(String composerID) {
		for (final IComposerExtension tool : getComposers()) {
			if (tool.getId().equals(composerID)) {
				return tool;
			}
		}
		CorePlugin.getDefault().logWarning(THE_REQUIRED_COMPOSER + composerID + IS_NOT_AVAILABLE_);
		return null;
	}

}
