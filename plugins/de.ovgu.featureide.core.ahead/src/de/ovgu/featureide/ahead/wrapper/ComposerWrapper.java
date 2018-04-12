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
package de.ovgu.featureide.ahead.wrapper;

import static de.ovgu.featureide.ahead.wrapper.AheadBuildErrorType.COMPOSER_ERROR;
import static de.ovgu.featureide.fm.core.localization.StringTable.DOES_NOT_EXIST;
import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_SKIPPED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_FEATURE_FOLDER_FOUND_IN_THE_JAK_FILE_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SOURCE_PATH_NOT_CONTAINED_IN_THE_JAK_FILE_PATH_;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNEXPECTED_ERROR_WHILE_PARSING;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeMap;

import org.eclipse.core.resources.IContainer;
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
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import jampack.Jampack;
import mixin.Mixin;

/**
 *
 * The class encapsulates everything that has to do with the composing step. It composes several given jak files. for each jak file all corresponding jak files
 * according to one configuration file were searched to compose them with the help of the Mixin class
 *
 * @author Tom Brosch
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 *
 */
public class ComposerWrapper {

	private static class FeatureVisitor implements IResourceVisitor {

		private final ComposerWrapper composer;

		public FeatureVisitor(ComposerWrapper composer) {
			this.composer = composer;
		}

		@Override
		public boolean visit(IResource resource) throws CoreException {
			if ((resource instanceof IFile) && "jak".equals(resource.getFileExtension())) {
				composer.addJakfileToCompose((IFile) resource);
			}
			return true;
		}
	}

	private final TreeMap<String, LinkedList<IFile>> absoluteJakFilenames = new TreeMap<>();

	private final LinkedList<IFolder> allFeatureFolders = new LinkedList<>();
	private final LinkedList<IFolder> featureFolders = new LinkedList<>();
	private final LinkedList<AheadBuildErrorListener> errorListeners = new LinkedList<>();
	private final LinkedList<IFile> composedFiles = new LinkedList<>();

	private final Mixin mixin = new Mixin();
	private final Jampack jampack = new Jampack();

	private final IFeatureProject featureProject;

	private final AbstractJakModelBuilder<?> jakModelBuilder;

	private IFolder compositionFolder = null;
	private IFile configFile = null;

	/**
	 * Creates a new instance of Composer
	 *
	 * @param featureProject
	 */
	public ComposerWrapper(IFeatureProject featureProject) {
		this.featureProject = featureProject;
		if ("Jampack".equals(featureProject.getCompositionMechanism())) {
			jakModelBuilder = new JampackJakModelBuilder(featureProject);
		} else {
			jakModelBuilder = new MixinJakModelBuilder(featureProject);
		}
	}

	void setCompositionFolder(IFolder folder) {
		compositionFolder = folder;
	}

	public IFile[] composeAll() throws IOException {
		return composeAll(configFile);
	}

	/**
	 * Composes all jak files for a given configuration file
	 *
	 * @param configFile
	 * @return Array of composed jakfiles
	 */
	// @SuppressWarnings("unchecked")
	public IFile[] composeAll(IFile configFile) throws IOException {
		// Set the given configuration file as the current one
		// Search in all feature directories for jakfiles and add
		// them to the composition list
		// Compose all and return the array of composed jakfiles

		setConfiguration(configFile);
		for (final IFolder featureFolder : new ArrayList<>(allFeatureFolders)) {
			try {
				if (featureFolder.exists()) {
					featureFolder.accept(new FeatureVisitor(this));
				} else if (FeatureUtils.extractConcreteFeaturesAsStringList(featureProject.getFeatureModel()).contains(featureFolder.getName())) {
					featureProject.createBuilderMarker(featureProject.getProject(), "Feature folder " + featureFolder.getName() + DOES_NOT_EXIST, 0,
							IMarker.SEVERITY_WARNING);
				}
			} catch (final CoreException e) {
				AheadCorePlugin.getDefault().logError(e);
			}
		}

		return compose();
	}

	/**
	 * Sets the current configuration file <br> This method has to be called before addJakfileToCompose
	 */
	void setConfiguration(IFile configFile) throws IOException {
		this.configFile = configFile;

		// Get feature folders
		// Get composition folder

		allFeatureFolders.clear();
		featureFolders.clear();

		if (configFile != null) {
			final Configuration configuration =
				new Configuration(featureProject.getFeatureModel(), Configuration.PARAM_IGNOREABSTRACT | Configuration.PARAM_LAZY);
			final ProblemList load = FileHandler.load(Paths.get(configFile.getLocationURI()), configuration, ConfigFormatManager.getInstance());
			if (!load.containsError()) {
				final List<IFeature> selectedFeatures = configuration.getSelectedFeatures();
				for (final IFeature feature : selectedFeatures) {
					if (feature.getStructure().isConcrete()) {
						final IFolder f = featureProject.getSourceFolder().getFolder(feature.getName());
						if (f != null) {
							featureFolders.add(f);
						}
					}
				}
			}
		}

		for (final IFolder folder : featureFolders) {
			allFeatureFolders.add(folder);
		}
		Collection<String> featureOrderList = featureProject.getFeatureModel().getFeatureOrderList();
		if ((featureOrderList == null) || featureOrderList.isEmpty()) {
			featureOrderList = FeatureUtils.extractConcreteFeaturesAsStringList(featureProject.getFeatureModel());
		}
		for (final String feature : featureOrderList) {
			final IFolder folder = featureProject.getSourceFolder().getFolder(feature);
			if (!allFeatureFolders.contains(folder)) {
				allFeatureFolders.add(folder);
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
	 * Adds a jakfile to the composition list <br> This method automaticaly searches for corresponding jakfiles in all specified feature folders
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

		final String srcFolderPath = featureProject.getSourceFolder().getRawLocation().toOSString();
		String jakFilePath = newJakFile.getRawLocation().toOSString();

		if (!jakFilePath.startsWith(srcFolderPath)) {
			AheadCorePlugin.getDefault().logWarning(SOURCE_PATH_NOT_CONTAINED_IN_THE_JAK_FILE_PATH_ + jakFilePath + FILE_SKIPPED_);
			return;
		}

		// Cut path to the source folder
		jakFilePath = jakFilePath.substring(srcFolderPath.length() + 1);

		// Cut feature folder
		final int pos = jakFilePath.indexOf(java.io.File.separator);

		if (pos < 0) {
			AheadCorePlugin.getDefault().logWarning(NO_FEATURE_FOLDER_FOUND_IN_THE_JAK_FILE_PATH_ + jakFilePath + FILE_SKIPPED_);
			return;
		}
		jakFilePath = jakFilePath.substring(pos + 1).replace("\\", "/");

		// don't add files twice
		if (absoluteJakFilenames.containsKey(jakFilePath)) {
			return;
		}

		final LinkedList<IFile> fileVector = new LinkedList<>();
		for (final IFolder root : allFeatureFolders) {
			final IFile jakFile = root.getFile(jakFilePath);
			if (jakFile.exists()) {
				fileVector.add(jakFile);
			}
		}
		// if (fileVector.size() == 0) {
		// this is the case if you try to add a jak file that lies in a
		// folder
		// that isn't contained in the configuration file
		// } else
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
		final IFile[] composedFilesArray = new IFile[composedFiles.size()];
		for (int i = 0; i < composedFilesArray.length; i++) {
			composedFilesArray[i] = composedFiles.get(i);
			try {
				composedFiles.get(i).refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (final CoreException e) {
				AheadCorePlugin.getDefault().logError(e);
			}
		}
		absoluteJakFilenames.clear();
		return composedFilesArray;
	}

	private void composeMixinJakFiles(IFolder compositionDir) {
		composedFiles.clear();
		jakModelBuilder.reset();
		final TreeMap<String, IFile> fileMap = new TreeMap<>();

		for (final String jakFile : new ArrayList<>(absoluteJakFilenames.keySet())) {
			final LinkedList<IFile> filesVec = absoluteJakFilenames.get(jakFile);
			final String[] files = new String[filesVec.size()];
			final IFile[] files2 = new IFile[filesVec.size()];
			for (int i = 0; i < filesVec.size(); i++) {
				final IFile file = filesVec.get(i);
				files[i] = file.getRawLocation().toOSString();
				files2[i] = file;
				fileMap.put(files[i], file);
			}

			final IFile newJakIFile = compositionDir.getFile(jakFile);
			try {
				final mixin.AST_Program[] composedASTs = new mixin.AST_Program[files.length];
				final mixin.AST_Program[] ownASTs = new mixin.AST_Program[files.length];
				mixin.compose(null, featureProject.getSourceFolder().getRawLocation().toOSString(), files, "x", composedASTs, ownASTs);

				// Add the currently composed class to the JakProject
				((MixinJakModelBuilder) jakModelBuilder).addClass(jakFile, filesVec, composedASTs, ownASTs);
				composedFiles.add(newJakIFile);

				if (configFile != null) {
					runMixin(files2);
				}
			} catch (final mixin.ExtendedParseException e) {
				handleErrorMessage(e, fileMap);
			} catch (final Throwable e) {
				AheadCorePlugin.getDefault().logError(e);
				handleErrorMessage(featureProject.getSourceFolder(), UNEXPECTED_ERROR_WHILE_PARSING + newJakIFile.getName(), 0);
			}
		}
	}

	private void composeJampackJakFiles(IFolder compositionDir) {
		composedFiles.clear();
		jakModelBuilder.reset();
		final TreeMap<String, IFile> fileMap = new TreeMap<>();

		for (final String jakFile : new ArrayList<>(absoluteJakFilenames.keySet())) {
			final LinkedList<IFile> filesVec = absoluteJakFilenames.get(jakFile);
			final String[] files = new String[filesVec.size()];
			final IFile[] files2 = new IFile[filesVec.size()];
			for (int i = 0; i < filesVec.size(); i++) {
				final IFile file = filesVec.get(i);
				files[i] = file.getRawLocation().toOSString();
				files2[i] = file;
				fileMap.put(files[i], file);
			}

			final IFile newJakIFile = compositionDir.getFile(jakFile);
			try {
				final jampack.AST_Program[] composedASTs = new jampack.AST_Program[files.length];
				final jampack.AST_Program[] ownASTs = new jampack.AST_Program[files.length];
				jampack.compose(null, featureProject.getSourceFolder().getRawLocation().toOSString(), files, "x", composedASTs, ownASTs);

				// Add the currently composed class to the JakProject
				((JampackJakModelBuilder) jakModelBuilder).addClass(jakFile, filesVec, composedASTs, ownASTs);
				composedFiles.add(newJakIFile);

				if (configFile != null) {
					runJampack(files2);
				}
			} catch (final jampack.ExtendedParseException e) {
				handleErrorMessage(e, fileMap);
			} catch (final Throwable e) {
				AheadCorePlugin.getDefault().logError(e);
				handleErrorMessage(featureProject.getSourceFolder(), UNEXPECTED_ERROR_WHILE_PARSING + newJakIFile.getName(), 0);
			}
		}
	}

	private void runMixin(IFile[] files) throws CoreException, ExitError {
		final String[] args = prepareArgs(files);
		if (args != null) {
			Mixin.main(args);
		}
	}

	private void runJampack(IFile[] files) throws CoreException, ExitError {
		final String[] args = prepareArgs(files);
		if (args != null) {
			Jampack.main(args);
		}
	}

	private String[] prepareArgs(IFile[] files) throws CoreException {
		files = removeUnselectedFeatures(files);
		if (files.length == 0) {
			return null;
		}

		final String layer = setLayer(files[0].getParent());
		int i = (layer != null) ? 4 : 2;

		final String[] args = new String[files.length + i];
		args[0] = "-f";
		args[1] = setOutputFolder(layer).getRawLocation().toOSString() + File.separator + files[0].getName();
		if (layer != null) {
			args[2] = "-a";
			args[3] = layer;
		}
		for (final IFile file : files) {
			args[i++] = file.getRawLocation().toOSString();
		}
		return args;
	}

	private IFile[] removeUnselectedFeatures(IFile[] files) {
		final ArrayList<IFile> selectedFiles = new ArrayList<>(files.length);
		for (final IFile file : files) {
			if (isSelectedFeature((IFolder) file.getParent())) {
				selectedFiles.add(file);
			}
		}
		return selectedFiles.toArray(new IFile[0]);
	}

	private boolean isSelectedFeature(IFolder folder) {
		if (featureProject.getSourceFolder().equals(folder.getParent())) {
			return featureFolders.contains(folder);
		}
		return isSelectedFeature((IFolder) folder.getParent());
	}

	private IFolder setOutputFolder(String layer) throws CoreException {
		IFolder outputFolder = compositionFolder;
		if (!outputFolder.exists()) {
			outputFolder.create(true, true, null);
		}
		if (layer != null) {
			final String[] packages = layer.split("[.]");
			for (final String pack : packages) {
				outputFolder = outputFolder.getFolder(pack);
				if (!outputFolder.exists()) {
					outputFolder.create(true, true, null);
				}
			}
		}
		return outputFolder;
	}

	private String setLayer(IContainer folder) {
		if (folder.getParent().equals(featureProject.getSourceFolder())) {
			return null;
		}
		if (setLayer(folder.getParent()) == null) {
			return folder.getName();
		}
		return setLayer(folder.getParent()) + "." + folder.getName();
	}

	private void handleErrorMessage(mixin.ExtendedParseException e, TreeMap<String, IFile> fileMap) {
		IFile source = null;
		final String filename = e.getFilename();
		if ((fileMap != null) && (filename != null) && fileMap.containsKey(filename)) {
			source = fileMap.get(filename);
		}
		handleErrorMessage(source, source != null ? e.getShortMessage() : e.getFullMessage(), e.getLineNumber());
	}

	private void handleErrorMessage(jampack.ExtendedParseException e, TreeMap<String, IFile> fileMap) {
		IFile source = null;
		final String filename = e.getFilename();
		if ((fileMap != null) && (filename != null) && fileMap.containsKey(filename)) {
			source = fileMap.get(filename);
		}
		handleErrorMessage(source, source != null ? e.getShortMessage() : e.getFullMessage(), e.getLineNumber());
	}

	private void handleErrorMessage(IResource source, String message, int lineNumber) {
		final AheadBuildErrorEvent evt = new AheadBuildErrorEvent(source, message, COMPOSER_ERROR, lineNumber);
		for (final AheadBuildErrorListener listener : errorListeners) {
			listener.parseErrorFound(evt);
		}
	}

	public void addBuildErrorListener(AheadBuildErrorListener listener) {
		if (!errorListeners.contains(listener)) {
			errorListeners.add(listener);
		}
	}

	public void removeBuildErrorListener(AheadBuildErrorListener listener) {
		errorListeners.remove(listener);
	}

}
