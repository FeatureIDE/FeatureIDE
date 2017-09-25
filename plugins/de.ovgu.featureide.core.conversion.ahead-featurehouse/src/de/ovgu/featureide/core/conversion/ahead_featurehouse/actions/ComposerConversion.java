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
package de.ovgu.featureide.core.conversion.ahead_featurehouse.actions;

import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * Abstract class for composer replacements.
 *
 * @author Jens Meinicke
 */
public abstract class ComposerConversion {

	IFeatureProject featureProject;

	/**
	 * Starts the conversion.
	 *
	 * @param project
	 */
	void startProjectConversion(IFeatureProject project) {
		featureProject = project;
		changeComposer(project);
		changeFiles(project.getSourceFolder());
		try {
			project.getProject().close(null);
			project.getProject().open(null);
		} catch (final CoreException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Iterates through all files of the feature folders.
	 *
	 * @param folder
	 *
	 */
	private void changeFiles(IFolder folder) {
		try {
			for (final IResource res : folder.members()) {
				if (res instanceof IFolder) {
					changeFiles((IFolder) res);
				} else {
					if (canConvert(res.getFileExtension())) {
						setFileText(changeFile(getFileText((IFile) res), (IFile) res), (IFile) res);
						replaceFileExtension((IFile) res);
					}
				}
			}
		} catch (final CoreException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Sets the context of the given file.
	 *
	 * @param newFileText The new context
	 * @param file
	 */
	private void setFileText(String newFileText, IFile file) {
		if (newFileText == null) {
			return;
		}
		FileWriter fw = null;
		try {
			fw = new FileWriter(file.getRawLocation().toFile());
			fw.write(newFileText);
		} catch (final IOException e) {
			AheadCorePlugin.getDefault().logError(e);
		} finally {
			if (fw != null) {
				try {
					fw.close();
				} catch (final IOException e) {
					AheadCorePlugin.getDefault().logError(e);
				}
			}
		}
	}

	/**
	 * @param res The file
	 * @return The context of the given file
	 */
	private String getFileText(IFile res) {
		Scanner scanner = null;
		try {
			scanner = new Scanner(res.getRawLocation().toFile(), "UTF-8");
			final StringBuffer buffer = new StringBuffer();
			while (scanner.hasNext()) {
				buffer.append(scanner.nextLine());
				buffer.append("\r\n");
			}
			return buffer.toString();
		} catch (final FileNotFoundException e) {
			AheadCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return "";
	}

	/**
	 * Changes the composer of the given project.
	 *
	 * @param project
	 *
	 */
	abstract void changeComposer(IFeatureProject project);

	/**
	 * Changes the context of the given file.
	 *
	 * @param fileText the context
	 * @param file The file
	 * @return The replaced context
	 */
	public abstract String changeFile(String fileText, IFile file);

	/**
	 * Replaces the file extension of the given file.
	 *
	 * @param file
	 */
	abstract void replaceFileExtension(IFile file);

	/**
	 * @param fileExtension
	 * @return <code>true</code> if the new composer can convert the given file extension
	 */
	abstract boolean canConvert(String fileExtension);
}
