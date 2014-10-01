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
package de.ovgu.featureide.ahead.wrapper;

import static de.ovgu.featureide.ahead.wrapper.AheadBuildErrorType.COMPOSER_ERROR;
import jampack.Jampack;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeMap;

import mixin.Mixin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;

import Jakarta.util.ExitError;
import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.ahead.model.AbstractJakModelBuilder;
import de.ovgu.featureide.ahead.model.JampackJakModelBuilder;
import de.ovgu.featureide.ahead.model.MixinJakModelBuilder;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * 
 * The class encapsulates everything that has to do with the composing step. It
 * composes several given jak files. for each jak file all corresponding jak
 * files according to one configuration file were searched to compose them with the
 * help of the Mixin class
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * 
 */
public class ComposerWrapper {

	private LinkedList<AheadBuildErrorListener> errorListeners;

	private TreeMap<String, LinkedList<IFile>> absoluteJakFilenames;

	private LinkedList<IFolder> allFeatureFolders;
	private LinkedList<IFolder> featureFolders;

	private Mixin mixin = new Mixin();	
	private Jampack jampack = new Jampack();
	
	private LinkedList<IFile> composedFiles;

	private IFolder compositionFolder;

	private IFile configFile;

	private IFeatureProject featureProject;

	private AbstractJakModelBuilder<?> jakModelBuilder;

	/**
	 * Creates a new instance of Composer
	 * 
	 * @param featureProject
	 */
	public ComposerWrapper(IFeatureProject featureProject) {
		absoluteJakFilenames = new TreeMap<String, LinkedList<IFile>>();
		composedFiles = new LinkedList<IFile>();
		allFeatureFolders = new LinkedList<IFolder>();
		featureFolders = new LinkedList<IFolder>();
		compositionFolder = null;
		configFile = null;
		errorListeners = new LinkedList<AheadBuildErrorListener>();
		this.featureProject = featureProject;
		if (jakModelBuilder == null) {
			if ("Jampack".equals(featureProject.getCompositionMechanism())) {
				jakModelBuilder = new JampackJakModelBuilder(featureProject);
			} else {
				jakModelBuilder = new MixinJakModelBuilder(featureProject);
			}
		}
	}
	
	void setCompositionFolder(IFolder folder) {
		compositionFolder = folder;
	}

	public IFile[] composeAll() throws IOException {
		return composeAll(configFile);
	}

	private static class FeatureVisitor implements IResourceVisitor {
		private ComposerWrapper composer;

		public FeatureVisitor(ComposerWrapper composer) {
			this.composer = composer;
		}

		public boolean visit(IResource resource) throws CoreException {
			if (resource instanceof IFile
					&& "jak".equals(resource.getFileExtension())) {
				composer.addJakfileToCompose((IFile) resource);
			}
			return true;
		}
	}

	/**
	 * Composes all jak files for a given configuration file
	 * 
	 * @param configFile
	 * @return Array of composed jakfiles
	 */
	@SuppressWarnings("unchecked")
	public IFile[] composeAll(IFile configFile) throws IOException {
		// Set the given configuration file as the current one
		// Search in all feature directories for jakfiles and add
		// them to the composition list
		// Compose all and return the array of composed jakfiles

		setConfiguration(configFile);
		for (IFolder featureFolder : (LinkedList<IFolder>)allFeatureFolders.clone()) {
			try {
				if (featureFolder.exists())
					featureFolder.accept(new FeatureVisitor(this));
				else if (featureProject.getFeatureModel().getConcreteFeatureNames()
						.contains(featureFolder.getName()))
					featureProject.createBuilderMarker(featureProject
							.getProject(), "Feature folder "
							+ featureFolder.getName() + " does not exist", 0,
							IMarker.SEVERITY_WARNING);
			} catch (CoreException e) {
				AheadCorePlugin.getDefault().logError(e);
			}
		}

		return compose();
	}

	/**
	 * Sets the current configuration file <br>
	 * This method has to be called before addJakfileToCompose
	 */
	void setConfiguration(IFile configFile) throws IOException {
		this.configFile = configFile;

		// Get feature folders
		// Get composition folder

		BufferedReader reader = null;
		allFeatureFolders.clear();
		featureFolders.clear();
		IFile config;
		if (configFile == null) {
			config = featureProject.getCurrentConfiguration();
		} else {
			config = configFile;
		}
		if (config != null) {
			try {
				reader = new BufferedReader(new FileReader(config
						.getRawLocation().toFile()));
				String line = null;
				while ((line = reader.readLine()) != null) {
					if (line.startsWith("#"))
						continue;
					IFolder f = featureProject.getSourceFolder().getFolder(line);
					if (f != null) {
						featureFolders.add(f);
					}
				}
			} finally {
				if (reader != null) { 
					reader.close();
				}
			}
		}
//		File file = featureProject.getProject().getLocation().toFile();
//		String fileSep = System.getProperty("file.separator");
//		file = new File(file.toString() + fileSep + ".order");
		/** replaced: list -> featuremodel.featurelist
		ArrayList<String> list = null;
		if (file.exists()){
			FeatureOrderReader reader2 = new FeatureOrderReader(
					featureProject.getProject().getLocation().toFile());
			list = reader2.featureOrderRead();
		}*/
		List<String> featureOrderList = featureProject.getFeatureModel().getFeatureOrderList();
		for (IFolder folder : featureFolders) {
			allFeatureFolders.add(folder);
		}
		if (featureOrderList == null || featureOrderList.isEmpty()) {	
			for (String feature : featureProject.getFeatureModel().getConcreteFeatureNames()) {
				IFolder folder = featureProject.getSourceFolder().getFolder(feature);
				if (!allFeatureFolders.contains(folder)) {
					allFeatureFolders.add(folder);
				}
			}
		} else {
			for (String feature : featureOrderList) {
				IFolder folder = featureProject.getSourceFolder().getFolder(feature);
				if (!allFeatureFolders.contains(folder)) {
					allFeatureFolders.add(folder);
				}
			}
		}
		if (compositionFolder == null) {
			compositionFolder = featureProject.getBuildFolder();
		}
	}

	/**
	 * Returns the current configuration file
	 * 
	 * @return the current configuration file
	 */
	public IFile getConfiguration() {
		return configFile;
	}

	/**
	 * Adds a jakfile to the composition list <br>
	 * This method automaticaly searches for corresponding jakfiles in all
	 * specified feature folders
	 * 
	 * @param newJakFile
	 * @throws ComposerException
	 */
	void addJakfileToCompose(IFile newJakFile) {
		// Find out the feature this file belongs to
		// Get the path relative to this folder
		// Search in all other feature folders for this file
		// Store all corresponding file in Vector<IFile> with
		// the relative filename as the key

		String srcFolderPath = featureProject.getSourceFolder()
				.getRawLocation().toOSString();
		String jakFilePath = newJakFile.getRawLocation().toOSString();

		if (!jakFilePath.startsWith(srcFolderPath)) {
			AheadCorePlugin.getDefault().logWarning("Source path not contained in the Jak file path '"
							+ jakFilePath + "'. File skipped.");
			return;
		}

		// Cut path to the source folder
		jakFilePath = jakFilePath.substring(srcFolderPath.length() + 1);

		// Cut feature folder
		int pos = jakFilePath.indexOf(java.io.File.separator);

		if (pos < 0) {
			AheadCorePlugin.getDefault().logWarning("No feature folder found in the Jak file path '"
					+ jakFilePath + "'. File skipped.");
			return;
		}
		jakFilePath = jakFilePath.substring(pos + 1).replace("\\", "/");

		// don't add files twice
		if (absoluteJakFilenames.containsKey(jakFilePath))
			return;

		LinkedList<IFile> fileVector = new LinkedList<IFile>();
		for (IFolder root : allFeatureFolders) {
			IFile jakFile = root.getFile(jakFilePath);
			if (jakFile.exists())
				fileVector.add(jakFile);
		}
		//if (fileVector.size() == 0) {
			// this is the case if you try to add a jak file that lies in a
			// folder
			// that isn't contained in the configuration file
	//	} else
			absoluteJakFilenames.put(jakFilePath, fileVector);
	}

	public IFile[] compose() {
		// decide method to call based on composition tool
		if ("Jampack".equals(featureProject.getCompositionMechanism())) {
			composeJampackJakFiles(compositionFolder);
		} else {
			composeMixinJakFiles(compositionFolder);
		}
		jakModelBuilder.addArbitraryFiles();
		IFile[] composedFilesArray = new IFile[composedFiles.size()];
		for (int i = 0; i < composedFilesArray.length; i++) {
			composedFilesArray[i] = composedFiles.get(i);
			try {
				composedFiles.get(i).refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				AheadCorePlugin.getDefault().logError(e);
			}
		}
		absoluteJakFilenames.clear();
		return composedFilesArray;
	}

	
	@SuppressWarnings("unchecked")
	private void composeMixinJakFiles(IFolder compositionDir) {
		composedFiles.clear();
		jakModelBuilder.reset();
		TreeMap<String, IFile> fileMap = new TreeMap<String, IFile>();
		
		for (String jakFile : ((TreeMap<String, LinkedList<IFile>>)absoluteJakFilenames.clone()).keySet()) {
			LinkedList<IFile> filesVec = absoluteJakFilenames.get(jakFile);
			String[] files = new String[filesVec.size()];
			IFile[] files2  = new IFile[filesVec.size()];
			for (int i = 0; i < filesVec.size(); i++) {
				files[i] = filesVec.get(i).getRawLocation().toOSString();
				files2[i] = filesVec.get(i);
				fileMap.put(files[i], filesVec.get(i));
			}

			IFile newJakIFile = compositionDir.getFile(jakFile);
			try {
				mixin.AST_Program[] composedASTs = new mixin.AST_Program[files.length];
				mixin.AST_Program[] ownASTs = new mixin.AST_Program[files.length];
				mixin.compose(null, featureProject.getSourceFolder().getRawLocation().toOSString(),
						files, "x", composedASTs, ownASTs);

				// Add the currently composed class to the JakProject
				((MixinJakModelBuilder) jakModelBuilder).addClass(jakFile, filesVec, composedASTs, ownASTs);
				composedFiles.add(newJakIFile);

				try {
					if (configFile != null) {
						runMixin(files2);
					}
				} catch (CoreException e) {
					AheadCorePlugin.getDefault().logError(e);
				}
			} catch (mixin.ExtendedParseException e) {
				handleErrorMessage(e, fileMap);
			} catch (Exception e) {
				AheadCorePlugin.getDefault().logError(e);
				handleErrorMessage(featureProject.getSourceFolder(),
						"Unexpected error while parsing "
								+ newJakIFile.getName(), 0);
			}
		}
	}

	
	@SuppressWarnings("unchecked")
	private void composeJampackJakFiles(IFolder compositionDir) {
		composedFiles.clear();
		jakModelBuilder.reset();
		TreeMap<String, IFile> fileMap = new TreeMap<String, IFile>();
		
		for (String jakFile : ((TreeMap<String, LinkedList<IFile>>)absoluteJakFilenames.clone()).keySet()) {
			LinkedList<IFile> filesVec = absoluteJakFilenames.get(jakFile);
			String[] files = new String[filesVec.size()];
			IFile[] files2  = new IFile[filesVec.size()];
			for (int i = 0; i < filesVec.size(); i++) {
				files[i] = filesVec.get(i).getRawLocation().toOSString();
				files2[i] = filesVec.get(i);
				fileMap.put(files[i], filesVec.get(i));
			}

			IFile newJakIFile = compositionDir.getFile(jakFile);
			try {
				jampack.AST_Program[] composedASTs = new jampack.AST_Program[files.length];
				jampack.AST_Program[] ownASTs = new jampack.AST_Program[files.length];
				jampack.compose(null, featureProject.getSourceFolder().getRawLocation().toOSString(),
						files, "x", composedASTs, ownASTs);

				// Add the currently composed class to the JakProject
				((JampackJakModelBuilder) jakModelBuilder).addClass(jakFile, filesVec, composedASTs, ownASTs);
				composedFiles.add(newJakIFile);

				try {
					if (configFile != null) {
						runJampack(files2);
					}
				} catch (CoreException e) {
					AheadCorePlugin.getDefault().logError(e);
				}
			} catch (jampack.ExtendedParseException e) {
				handleErrorMessage(e, fileMap);
			} catch (Exception e) {
				AheadCorePlugin.getDefault().logError(e);
				handleErrorMessage(featureProject.getSourceFolder(),
						"Unexpected error while parsing "
								+ newJakIFile.getName(), 0);
			}
		}
	}
	
	private void runMixin(IFile[] files) throws CoreException {
		files = removeUnselectedFeatures(files);
		if (files.length == 0) {
			return;
		}
		String layer = setLayer((IFolder)files[0].getParent());
		int i = 4;
		if (layer == null) {
			i = 2;
		}
		String[] args = new String[files.length + i];
		IFolder outputfolder = setOutputFolder(layer);
		args[0] = "-f";
		args[1] = outputfolder.getRawLocation().toOSString() + File.separator + files[0].getName(); 
		if (layer != null) {
			args[2] = "-a";
			args[3] = layer;
		}
		for (IFile file : files) {
			
			args[i] = file.getRawLocation().toOSString();
			i++;
		}
		
		//run Mixin
		try {
			Mixin.main(args);
		} catch (ExitError e) {
			AheadCorePlugin.getDefault().logError(e);
		}	
		
	}

	private void runJampack(IFile[] files) throws CoreException {
		files = removeUnselectedFeatures(files);
		if (files.length == 0) {
			return;
		}
		String layer = setLayer((IFolder)files[0].getParent());
		int i = 4;
		if (layer == null) {
			i = 2;
		}
		String[] args = new String[files.length + i];
		IFolder outputfolder = setOutputFolder(layer);
		args[0] = "-f";
		args[1] = outputfolder.getRawLocation().toOSString() + File.separator + files[0].getName(); 
		if (layer != null) {
			args[2] = "-a";
			args[3] = layer;
		}
		for (IFile file : files) {
			
			args[i] = file.getRawLocation().toOSString();
			i++;
		}
		
		//run Jampack
		try {
			Jampack.main(args);
		} catch (ExitError e) {
			AheadCorePlugin.getDefault().logError(e);
		}	
		
	}
	
	private IFile[] removeUnselectedFeatures(IFile[] files) {
		ArrayList<IFile> selectedFiles = new ArrayList<IFile>();
		for (IFile file : files) {
			if (isSelectedFeature((IFolder)file.getParent()))
				selectedFiles.add(file);
		}
		IFile[] featureFiles = new IFile[selectedFiles.size()];
		int i = 0;
		for (IFile file : selectedFiles) {
			featureFiles[i] = file;
			i++;
		}
		return featureFiles;
	}

	private boolean isSelectedFeature(IFolder folder) {
		if (featureProject.getSourceFolder().equals(folder.getParent())) {
			if (featureFolders.contains(folder)) {
				return true;
			}
			return false;
		}
		return isSelectedFeature((IFolder)folder.getParent());
	}

	private IFolder setOutputFolder(String layer) throws CoreException {
		IFolder outputFolder = compositionFolder;//XXXfeatureProject.getBuildFolder(); 
		if (layer == null)
			return outputFolder;
		
		String[] packages = layer.split("[.]");
		for (String pack : packages) {
			outputFolder = outputFolder.getFolder(pack);
			if (!outputFolder.exists())
				outputFolder.create(true, true, null);
		}
		return outputFolder;
	}

	private String setLayer(IFolder folder) {
		if (((IFolder)folder.getParent()).equals(featureProject.getSourceFolder()))
			return null;
		if (setLayer((IFolder)folder.getParent()) == null)
			return folder.getName();
		return setLayer((IFolder)folder.getParent()) + "." + folder.getName();
	}

	private void handleErrorMessage(mixin.ExtendedParseException e,
			TreeMap<String, IFile> fileMap) {
		IFile source = null;
		String filename = e.getFilename();
		if (fileMap != null && filename != null && fileMap.containsKey(filename)) {
			source = fileMap.get(filename);
		}
		String message = source != null ? e.getShortMessage() : e.getFullMessage();
		handleErrorMessage(source, message, e.getLineNumber());
	}

	private void handleErrorMessage(jampack.ExtendedParseException e,
			TreeMap<String, IFile> fileMap) {
		IFile source = null;
		String filename = e.getFilename();
		if (fileMap != null && filename != null && fileMap.containsKey(filename))
			source = fileMap.get(filename);
		String message = source != null ? e.getShortMessage() : e
				.getFullMessage();
		handleErrorMessage(source, message, e.getLineNumber());
	}
	
	private void handleErrorMessage(IResource source, String message,
			int lineNumber) {
		AheadBuildErrorEvent evt = new AheadBuildErrorEvent(source, message,
				COMPOSER_ERROR, lineNumber);
		for (AheadBuildErrorListener listener : errorListeners)
			listener.parseErrorFound(evt);
	}

	public void addBuildErrorListener(AheadBuildErrorListener listener) {
		if (!errorListeners.contains(listener))
			errorListeners.add(listener);
	}

	public void removeBuildErrorListener(AheadBuildErrorListener listener) {
		errorListeners.remove(listener);
	}

}
