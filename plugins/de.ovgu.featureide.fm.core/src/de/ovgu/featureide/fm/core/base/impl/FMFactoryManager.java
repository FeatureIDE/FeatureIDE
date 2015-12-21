/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.ArrayList;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;

/**
 * Returns custom factories to create {@link IFeatureModel}, {@link IFeature}, and {@link IConstraint} instances.
 * 
 * @author Sebastian Krieter
 */
public final class FMFactoryManager {
	
	private static ArrayList<IFeatureModelFactory> cachedProviders = null;
	
//	private void loadProviders(String pluginID, String extensionPointID) {
//		ArrayList<?> cachedProviders = new ArrayList<>();
//		IExtension[] extensions = Platform.getExtensionRegistry().getExtensionPoint(pluginID, extensionPointID).getExtensions();
//		for (IExtension extension : extensions) {
//			IConfigurationElement[] configurationElements = extension.getConfigurationElements();
//			for (IConfigurationElement configurationElement : configurationElements) {
//				IFeatureModelFactory proxy = parseExtension(configurationElement);
//				if (proxy != null) {
//					cachedProviders.add(proxy);
//				}
//			}
//		}
//	}
//	
//	protected IFeatureModelFactory parseExtension(IConfigurationElement configurationElement) {
//		try {
//			return (IFeatureModelFactory) configurationElement.createExecutableExtension("class");
//		} catch (CoreException e) {
//			FMCorePlugin.getDefault().logError(e);
//		} catch (ClassCastException e) {
//			FMCorePlugin.getDefault().logError(e);
//		}
//	}

	private FMFactoryManager() {
	}

	private final static IFeatureModelFactory[] factoryArray;
	static {
		factoryArray = new IFeatureModelFactory[2];
		factoryArray[0] = DefaultFeatureModelFactory.getInstance();
		factoryArray[1] = ExtendedFeatureModelFactory.getInstance();
	}

	public static IFeatureModelFactory getFactory() {
		return DefaultFeatureModelFactory.getInstance();
	}

	public static IFeatureModelFactory getFactory(String id) {
		for (IFeatureModelFactory factory : factoryArray) {
			if (factory.getId().equals(id)) {
				return factory;
			}
		}
		throw new RuntimeException("No factory found for ID " + id);
	}

}
