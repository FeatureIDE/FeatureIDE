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
package de.ovgu.featureide.fm.core.init;

import de.ovgu.featureide.fm.core.EclipseExtensionLoader;
import de.ovgu.featureide.fm.core.EclipseLogger;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFactory;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.ConfigurationFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.DefaultConfigurationFactory;
import de.ovgu.featureide.fm.core.base.impl.EclipseFactoryWorkspaceProvider;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.dimacs.DIMACSFormat;
import de.ovgu.featureide.fm.core.job.LongRunningEclipse;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.preferences.DIMACSOmitRootPreference;

/**
 * The library object for the fm.core plug-in when using the Eclipse platform.
 *
 * @author Sebastian Krieter
 */
public class FMCoreEclipseLibrary implements ILibrary {

	private static FMCoreEclipseLibrary instance;

	public static FMCoreEclipseLibrary getInstance() {
		if (instance == null) {
			instance = new FMCoreEclipseLibrary();
		}
		return instance;
	}

	private FMCoreEclipseLibrary() {}

	@Override
	public void install() {
		FileSystem.INSTANCE = new EclipseFileSystem();
		LongRunningWrapper.INSTANCE = new LongRunningEclipse();
		Logger.logger = new EclipseLogger();

		FMFactoryManager.getInstance().addExtensions(new EclipseExtensionLoader<IFactory<IFeatureModel>>(PluginID.PLUGIN_ID,
				IFeatureModelFactory.extensionPointID, IFeatureModelFactory.extensionID, IFeatureModelFactory.class));
		FMFactoryManager.getInstance().setWorkspaceLoader(new EclipseFactoryWorkspaceProvider("featureModel"));

		ConfigurationFactoryManager.getInstance().addExtension(DefaultConfigurationFactory.getInstance());
		ConfigurationFactoryManager.getInstance().setWorkspaceLoader(new EclipseFactoryWorkspaceProvider("configuration"));

		FMFormatManager.getInstance().addExtensions(new EclipseExtensionLoader<IPersistentFormat<IFeatureModel>>(PluginID.PLUGIN_ID,
				IFeatureModelFormat.extensionPointID, IFeatureModelFormat.extensionID, IFeatureModelFormat.class));

		ConfigFormatManager.getInstance().addExtensions(new EclipseExtensionLoader<IPersistentFormat<Configuration>>(PluginID.PLUGIN_ID,
				IConfigurationFormat.extensionPointID, IConfigurationFormat.extensionID, IConfigurationFormat.class));

		try {
			((DIMACSFormat) FMFormatManager.getInstance().getExtension(DIMACSFormat.ID)).setOmitDummyRoot(DIMACSOmitRootPreference.getInstance().get());
		} catch (final NoSuchExtensionException e) {
			Logger.logError(e);
		}
	}

	@Override
	public void uninstall() {
		FMFactoryManager.getInstance().save();
		ConfigurationFactoryManager.getInstance().save();
	}

}
