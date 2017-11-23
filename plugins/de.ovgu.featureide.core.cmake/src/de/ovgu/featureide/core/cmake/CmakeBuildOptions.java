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
package de.ovgu.featureide.core.cmake;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.runtime.activator.RuntimeCorePlugin;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;


/**
 * 
 * CmakeBuildOptions Composer creates .cmake files from actual configuration.
 * This files can then be used during the build process of the products
 * 
 */
@SuppressWarnings("restriction")
public class CmakeBuildOptions extends ComposerExtensionClass {

	final private String CMAKE_OPTION_PATTERN = "set(%s \"%s\" CACHE PATH \"\") \n";
	final private String CMALE_OPTION_ENABLED = "ON";
	final private String CMALE_OPTION_DISABLED = "OFF";
	
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionClass#performFullBuild(org.eclipse.core.resources.IFile)
	 */
	@Override
	public void performFullBuild(IFile config) {
		// TODO Auto-generated method stub		

		final Configuration configuration = readConfig();				
		final String configName = featureProject.getCurrentConfiguration().getName();

		// Add source path to referenced project location
		IFile file = featureProject.getSourceFolder().getFile(configName + ".cmake");
		
		String configString = "";
		for (final SelectableFeature f : configuration.getFeatures()) {
			if (!f.getFeature().getStructure().isAbstract()) {
				configString += String.format(CMAKE_OPTION_PATTERN
												, f.getFeature().getName().toUpperCase()
												, f.getSelection() == Selection.SELECTED ? CMALE_OPTION_ENABLED : CMALE_OPTION_DISABLED);														
			}
		}
						
		InputStream inputStream = new ByteArrayInputStream(configString.getBytes(StandardCharsets.UTF_8));
					
		if (file.exists()) {
			try {
				file.setContents(inputStream, IResource.FORCE, null);
			} catch (final CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		} else {
			createFile(file, inputStream);
		}

	}

	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

	@Override
	public boolean createFolderForFeatures() {
		return false;
	}	
	
	/**
	 * Reads and returns current feature config.
	 * 
	 * @return
	 */
	private Configuration readConfig() {
		final Configuration featureProjectConfig = new Configuration(featureProject.getFeatureModel());
		final Path configPath = Paths.get(featureProject.getCurrentConfiguration().getLocationURI());
		SimpleFileHandler.load(configPath, featureProjectConfig, ConfigFormatManager.getInstance());
		return featureProjectConfig;
	}

	private void createFile(final IFile file, final InputStream stream) {
		if (file != null) {
			try {
				file.create(stream, true, null);
			} catch (final CoreException e) {
				RuntimeCorePlugin.getDefault().logError(e);
			}
		}
	}

	
}