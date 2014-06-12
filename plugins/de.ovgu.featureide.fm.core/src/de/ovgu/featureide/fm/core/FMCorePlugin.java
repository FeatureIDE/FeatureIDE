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

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.Collection;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.osgi.framework.BundleContext;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.ModelIOFactory;

/**
 * The activator class controls the plug-in life cycle.
 * 
 * @author Thomas Thuem
 */
public class FMCorePlugin extends AbstractCorePlugin {

	public static final String PLUGIN_ID = "de.ovgu.featureide.fm.core";
	
	private static FMCorePlugin plugin;

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.plugin.AbstractUIPlugin#getID()
	 */
	@Override
	public String getID() {
		return PLUGIN_ID;
	}
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	public static FMCorePlugin getDefault() {
		return plugin;
	}
	
	public void analyzeModel(IFile file) {
		logInfo("Reading Model File...");
		final IContainer outputDir = file.getParent();
		if (outputDir == null || !(outputDir instanceof IFolder)) {
			return;
		}
		
		final int modelType = ModelIOFactory.getTypeByFileName(file.getName());
		if (modelType == ModelIOFactory.TYPE_UNKNOWN) {
			return;
		}
		final FeatureModel fm = ModelIOFactory.getNewFeatureModel(modelType);
		final AbstractFeatureModelReader reader = ModelIOFactory.getModelReader(fm, modelType);
		
		try {
			reader.readFromFile(file.getLocation().toFile());
			FeatureModelAnalyzer fma = new FeatureModelAnalyzer(fm);
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

			Collection<Feature> analyzedFeatures = fma.getCoreFeatures();
			sb.append("Core Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (Feature coreFeature : analyzedFeatures) {
				sb.append(coreFeature.getName());
				sb.append(", ");
			}
			analyzedFeatures = fma.getDeadFeatures();
			sb.append("\nDead Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (Feature deadFeature : analyzedFeatures) {
				sb.append(deadFeature.getName());
				sb.append(", ");
			}
			analyzedFeatures = fma.getFalseOptionalFeatures();
			sb.append("\nFO Features (");
			sb.append(analyzedFeatures.size());
			sb.append("): ");
			for (Feature foFeature : analyzedFeatures) {
				sb.append(foFeature.getName());
				sb.append(", ");
			}
			sb.append("\n");

			final IFile outputFile = ((IFolder) outputDir).getFile(file.getName() + "_output.txt");
			final InputStream inputStream = new ByteArrayInputStream(
					sb.toString().getBytes(Charset.defaultCharset()));
			if (outputFile.isAccessible()) {
				outputFile.setContents(inputStream, false, true, null);
			} else {
				outputFile.create(inputStream, true, null);
			}
			logInfo("Printed Output File.");
		} catch (Exception e) {
			logError(e);
		}
	}
}
