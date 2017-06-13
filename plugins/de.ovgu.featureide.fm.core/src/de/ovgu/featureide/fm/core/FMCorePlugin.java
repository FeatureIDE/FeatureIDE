/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.PRINTED_OUTPUT_FILE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.READING_MODEL_FILE___;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.nio.file.Paths;
import java.util.Collection;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.EclipseFactoryWorkspaceProvider;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelFormat;
import de.ovgu.featureide.fm.core.job.LongRunningEclipse;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Thomas Thuem
 */
public class FMCorePlugin extends AbstractCorePlugin {

	private static FMCorePlugin plugin;

	@Override
	public String getID() {
		return PluginID.PLUGIN_ID;
	}

	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;

		FileSystem.INSTANCE = new EclipseFileSystem();
		LongRunningWrapper.INSTANCE = new LongRunningEclipse();

		FMFactoryManager.setExtensionLoader(new EclipseExtensionLoader<>(PluginID.PLUGIN_ID, IFeatureModelFactory.extensionPointID,
				IFeatureModelFactory.extensionID, IFeatureModelFactory.class));
		FMFormatManager.setExtensionLoader(new EclipseExtensionLoader<>(PluginID.PLUGIN_ID, IFeatureModelFormat.extensionPointID,
				IFeatureModelFormat.extensionID, IFeatureModelFormat.class));
		ConfigFormatManager.setExtensionLoader(new EclipseExtensionLoader<>(PluginID.PLUGIN_ID, IConfigurationFormat.extensionPointID,
				IConfigurationFormat.extensionID, IConfigurationFormat.class));

		//		ConfigFormatManager.setExtensionLoader(new CoreExtensionLoader<>(new DefaultFormat(), new FeatureIDEFormat(), new EquationFormat(), new ExpressionFormat()));
		//		FMFormatManager.setExtensionLoader(new CoreExtensionLoader<>(new XmlFeatureModelFormat(), new SimpleVelvetFeatureModelFormat(), new DIMACSFormat(), new SXFMFormat(), new GuidslFormat()));
		//		FMFactoryManager.setExtensionLoader(new CoreExtensionLoader<>(new DefaultFeatureModelFactory(), new ExtendedFeatureModelFactory()));

		Logger.logger = new EclipseLogger();
		FMFactoryManager.factoryWorkspaceProvider = new EclipseFactoryWorkspaceProvider();

		if (!FMFactoryManager.factoryWorkspaceProvider.load()) {
			FMFactoryManager.factoryWorkspaceProvider.getFactoryWorkspace().assignID(VelvetFeatureModelFormat.ID, ExtendedFeatureModelFactory.ID);
		}
	}

	public void stop(BundleContext context) throws Exception {
		FMFactoryManager.factoryWorkspaceProvider.save();
		plugin = null;
		super.stop(context);
	}

	public static FMCorePlugin getDefault() {
		return plugin;
	}

	public void analyzeModel(IFile file) {
		logInfo(READING_MODEL_FILE___);
		final IContainer outputDir = file.getParent();
		if (outputDir == null || !(outputDir instanceof IFolder)) {
			return;
		}

		final IPersistentFormat<IFeatureModel> format = FeatureModelManager.getFormat(file.getName());
		if (format == null) {
			return;
		}

		FeatureProject featureProject = ProjectManager.getProject(Paths.get(file.getProject().getLocationURI()));

		final IFeatureModel fm = featureProject.getStatus().getFeatureModel();
		try {
			FeatureModelAnalyzer fma = featureProject.getStatus().getAnalyzer();
			fma.analyzeFeatureModel(null);

			final StringBuilder sb = new StringBuilder();
			sb.append("Number Features: ");
			sb.append(fm.getNumberOfFeatures());
			sb.append(" (");
			sb.append(fma.countConcreteFeatures());
			sb.append(")\n");

			if (fm instanceof ExtendedFeatureModel) {
				ExtendedFeatureModel extFeatureModel = (ExtendedFeatureModel) fm;
				int countInherited = 0;
				int countInstances = 0;
				for (UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
					switch (usedModel.getType()) {
					case ExtendedFeature.TYPE_INHERITED:
						countInherited++;
						break;
					case ExtendedFeature.TYPE_INSTANCE:
						countInstances++;
						break;
					}
				}
				sb.append("Number Instances: ");
				sb.append(countInstances);
				sb.append("\n");
				sb.append("Number Inherited: ");
				sb.append(countInherited);
				sb.append("\n");
			}

			Collection<IFeature> analyzedFeatures = fma.getCoreFeatures();
			sb.append("Core Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (IFeature coreFeature : analyzedFeatures) {
				sb.append(coreFeature.getName());
				sb.append(", ");
			}
			analyzedFeatures = fma.getDeadFeatures();
			sb.append("\nDead Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (IFeature deadFeature : analyzedFeatures) {
				sb.append(deadFeature.getName());
				sb.append(", ");
			}
			analyzedFeatures = fma.getFalseOptionalFeatures();
			sb.append("\nFO Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (IFeature foFeature : analyzedFeatures) {
				sb.append(foFeature.getName());
				sb.append(", ");
			}
			sb.append("\n");

			final IFile outputFile = ((IFolder) outputDir).getFile(file.getName() + "_output.txt");
			final InputStream inputStream = new ByteArrayInputStream(sb.toString().getBytes(Charset.defaultCharset()));
			if (outputFile.isAccessible()) {
				outputFile.setContents(inputStream, false, true, null);
			} else {
				outputFile.create(inputStream, true, null);
			}
			logInfo(PRINTED_OUTPUT_FILE_);
		} catch (Exception e) {
			logError(e);
		}
	}

}
