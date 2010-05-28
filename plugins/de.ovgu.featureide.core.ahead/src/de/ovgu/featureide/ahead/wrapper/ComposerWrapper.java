/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ahead.wrapper;

import static de.ovgu.featureide.ahead.wrapper.AheadBuildErrorType.COMPOSER_ERROR;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.TreeMap;

import mixin.AST_Program;
import mixin.ExtendedParseException;
import mixin.Mixin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.ResourceAttributes;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.ahead.model.JakModelBuilder;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * 
 * The class encapsulates everything that has to do with the composing step. It
 * composes several given jak files. for each jak file all corresponding jak
 * files according to one equation file were searched to compose them with the
 * help of the Mixin class
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * 
 */
public class ComposerWrapper {

	private LinkedList<AheadBuildErrorListener> errorListeners;

	private TreeMap<String, LinkedList<IFile>> absoluteJakFilenames;

	private LinkedList<IFolder> featureFolders;

	private Mixin mixin = new Mixin();

	private LinkedList<IFile> composedFiles;

	private IFolder compositionFolder;

	private IFile equationFile;

	private IFeatureProject featureProject;

	private JakModelBuilder jakModelBuilder;

	/**
	 * Creates a new instance of Composer
	 * 
	 * @param featureProject
	 */
	public ComposerWrapper(IFeatureProject featureProject) {
		absoluteJakFilenames = new TreeMap<String, LinkedList<IFile>>();
		composedFiles = new LinkedList<IFile>();
		featureFolders = new LinkedList<IFolder>();
		compositionFolder = null;
		equationFile = null;
		errorListeners = new LinkedList<AheadBuildErrorListener>();
		this.featureProject = featureProject;
		jakModelBuilder = new JakModelBuilder(this.featureProject);
	}

	public IFile[] composeAll() throws IOException {
		return composeAll(equationFile);
	}

	private class FeatureVisitor implements IResourceVisitor {
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
	 * Composes all jakfiles for a given equation file
	 * 
	 * @param equationFile
	 * @return Array of composed jakfiles
	 */
	public IFile[] composeAll(IFile equationFile) throws IOException {
		// Set the given equation file as the current one
		// Search in all feature directories for jakfiles and add
		// them to the composition list
		// Compose all and return the array of composed jakfiles

		setEquation(equationFile);
		for (IFolder featureFolder : featureFolders) {
			try {
				if (featureFolder.exists())
					featureFolder.accept(new FeatureVisitor(this));
				else if (featureProject.getFeatureModel().getLayerNames()
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
	 * Sets the current equation file <br>
	 * This method has to be called before addJakfileToCompose
	 */
	void setEquation(IFile equationFile) throws IOException {
		this.equationFile = equationFile;
		if (equationFile == null)
			return;

		// Get feature folders
		// Get composition folder

		BufferedReader reader = null;
		featureFolders.clear();

		reader = new BufferedReader(new FileReader(equationFile
				.getRawLocation().toFile()));
		String line = null;
		while ((line = reader.readLine()) != null) {
			if (line.startsWith("#"))
				continue;
			featureFolders
					.add(featureProject.getSourceFolder().getFolder(line));
		}
		reader.close();

		String compositionName = equationFile.getName().substring(0,
				equationFile.getName().lastIndexOf("."));
		compositionFolder = featureProject.getBuildFolder().getFolder(
				compositionName);
	}

	/**
	 * Returns the current equation file
	 * 
	 * @return the current equation file
	 */
	public IFile getEquation() {
		return equationFile;
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
			System.err
					.println("Source path not contained in the Jak file path '"
							+ jakFilePath + "'. File skipped.");
			return;
		}

		// Cut path to the source folder
		jakFilePath = jakFilePath.substring(srcFolderPath.length() + 1);

		// Cut feature folder
		int pos = jakFilePath.indexOf(java.io.File.separator);

		if (pos < 0) {
			System.err.println("No feature folder found in the Jak file path '"
					+ jakFilePath + "'. File skipped.");
			return;
		}
		jakFilePath = jakFilePath.substring(pos + 1);

		// don't add files twice
		if (absoluteJakFilenames.containsKey(jakFilePath))
			return;

		LinkedList<IFile> fileVector = new LinkedList<IFile>();
		for (IFolder root : featureFolders) {
			IFile jakFile = root.getFile(jakFilePath);
			if (jakFile.exists())
				fileVector.add(jakFile);
		}
		if (fileVector.size() == 0) {
			// this is the case if you try to add a jak file that lies in a
			// folder
			// that isn't contained in the equation file
		} else
			absoluteJakFilenames.put(jakFilePath, fileVector);
	}

	public IFile[] compose() {
		composeJakFiles(compositionFolder);
		IFile[] composedFilesArray = new IFile[composedFiles.size()];
		for (int i = 0; i < composedFilesArray.length; i++)
			composedFilesArray[i] = composedFiles.get(i);

		absoluteJakFilenames.clear();
		return composedFilesArray;
	}

	private void composeJakFiles(IFolder compositionDir) {
		composedFiles.clear();
		if (equationFile == null)
			return;
		String aspectName = equationFile.getName();
		aspectName = aspectName.substring(0, aspectName.lastIndexOf('.'));
		TreeMap<String, IFile> fileMap = new TreeMap<String, IFile>();
		jakModelBuilder.clearFeatures();
		for (String jakFile : absoluteJakFilenames.keySet()) {
			LinkedList<IFile> filesVec = absoluteJakFilenames.get(jakFile);
			String[] files = new String[filesVec.size()];
			for (int i = 0; i < filesVec.size(); i++) {
				files[i] = filesVec.get(i).getRawLocation().toOSString();
				fileMap.put(files[i], filesVec.get(i));
			}

			// Checks whether the directory exists, where the composed
			// jakfiles will be written to
			IFile newJakIFile = compositionDir.getFile(jakFile);
			File newJakFile = newJakIFile.getRawLocation().toFile();
			if (!newJakFile.getParentFile().isDirectory())
				newJakFile.getParentFile().mkdirs();
			try {
				AST_Program[] composedASTs = new AST_Program[files.length];
				AST_Program[] ownASTs = new AST_Program[files.length];
				mixin.compose(newJakFile.getAbsolutePath(), featureProject
						.getSourceFolder().getRawLocation().toOSString(),
						files, aspectName, composedASTs, ownASTs);

				// Add the currently composed class to the JakProject
				jakModelBuilder.addClass(jakFile, filesVec, composedASTs,
						ownASTs);
				composedFiles.add(newJakIFile);

				// debugTheAST(ownASTs[ownASTs.length - 1]);

			} catch (ExtendedParseException e) {
				handleErrorMessage(e, fileMap);
			} catch (Exception e) {
				handleErrorMessage(featureProject.getSourceFolder(),
						"Unexpected error while parsing "
								+ newJakFile.getName(), 0);
			}

			try {
				newJakIFile.refreshLocal(IResource.DEPTH_ZERO, null);
				if (newJakIFile.exists()) {
					newJakIFile.setDerived(true);
					ResourceAttributes attr = newJakIFile
							.getResourceAttributes();
					if (attr != null) {
						attr.setReadOnly(true);
						newJakIFile.setResourceAttributes(attr);
					}
				}
			} catch (CoreException e) {
				AheadCorePlugin.getDefault().logError(e);
			}
		}
	}

	private void handleErrorMessage(ExtendedParseException e,
			TreeMap<String, IFile> fileMap) {
		IFile source = null;
		if (fileMap.containsKey(e.getFilename()))
			source = fileMap.get(e.getFilename());
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
