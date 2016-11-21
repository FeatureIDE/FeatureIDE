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
package de.ovgu.featureide.deltamontiarc;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;

public class DeltaMontiArcComposer extends ComposerExtensionClass {

	private LinkedList<IFolder> featureFolders = new LinkedList<IFolder>();
	private IFolder outputFolder;
	private IFile configFile;
	
	@Override
	public boolean copyNotComposedFiles() {
		return true;
	}
	
	@Override
	public void performFullBuild(IFile config) {
		
		try {
			setConfiguration(config);
			buildDeltaConfiguration();
		} catch (IOException e) {
			DeltaMontiArcPlugin.getDefault().logError(e);
		}
	}
	
	private void setConfiguration(IFile configFile) throws IOException {
		this.configFile = configFile;
		// set feature folders for all features specified in config file
		featureFolders.clear();
		IFile config;
		if (configFile == null) {
			config = featureProject.getCurrentConfiguration();
		} else {
			config = configFile;
		}
		if (config == null) {
			return;
		}

		Configuration configuration = new Configuration(featureProject.getFeatureModel());
		ConfigurationReader reader = new ConfigurationReader(configuration);
		
		try {
			reader.readFromFile(config);
		} catch (CoreException e) {
			DeltaMontiArcPlugin.getDefault().logError(e);
		} catch (IOException e) {
			DeltaMontiArcPlugin.getDefault().logError(e);
		}
		for (Feature feature : configuration.getSelectedFeatures()) {
			featureFolders.add(featureProject.getSourceFolder().getFolder(feature.getName()));
		}
		
		// target folder to store the delta configuration
		outputFolder = featureProject.getBuildFolder();
	}
	
	private void buildDeltaConfiguration() {
		String configName = configFile.getName();
		int indexOfExt = configName.lastIndexOf(configFile.getFileExtension())-1;
		String productName = configName.substring(0, indexOfExt);
		List<String> deltaNames = getQualifiedDeltaNamesInFeatureFolders();
		IFile deltaConfig = outputFolder.getFile(productName+".delta");
		String contents = createConfigContents(productName, deltaNames);
		InputStream input = new ByteArrayInputStream(contents.toString().getBytes());
		try {
			deltaConfig.create(input, true, null);
		} catch (CoreException e) {
			DeltaMontiArcPlugin.getDefault().logError(e);
		}
	}
	
	private String createConfigContents(String configName, List<String> deltaNames) {
		StringBuilder contents = new StringBuilder();
		contents.append("deltaconfig ");
		contents.append(configName);
		contents.append(" {\n\t");
		String sep = "";
		for (String deltaName : deltaNames) {
			contents.append(sep);
			contents.append(deltaName);
			sep = ",\n\t";
		}
		contents.append("\n}");
		return contents.toString();
	}
	
	private List<String> getQualifiedDeltaNamesInFeatureFolders() {
		List<String> deltaNames = new ArrayList<String>();
		for (IFolder folder : featureFolders) {
			String fileName = folder.getRawLocation().toOSString();
			int startIndex = fileName.length()+1;
			for (File deltaFile : getFilesByFileEnding(new File(fileName), ".delta")) {
				String name = deltaFile.getAbsolutePath();
				int endIndex = name.lastIndexOf(".delta");
				name = name.substring(startIndex, endIndex).replace(File.separator, ".");
				if (!deltaNames.contains(name)) {
					deltaNames.add(name);
				}
			}
			
		}
		return deltaNames;
	}
	
    /**
     * Returns all files with the given file ending which are in
     * the given directory and its subdirectories
     * @param dir directory to start the search
     * @param ending file ending
     * @return list of files with given file ending
     */
    private List<File> getFilesByFileEnding(File dir, String ending) {
        List<File> files = new ArrayList<File>();
        if (dir.exists() && dir.isDirectory()) {
            for (File x : dir.listFiles()) {
                if (x.isDirectory()) {
                    files.addAll(getFilesByFileEnding(x, ending));
                }
                else if (x.getName().toLowerCase().endsWith(ending)) {
                    files.add(x);
                }
            }
            
        }
        return files;
    }
}
