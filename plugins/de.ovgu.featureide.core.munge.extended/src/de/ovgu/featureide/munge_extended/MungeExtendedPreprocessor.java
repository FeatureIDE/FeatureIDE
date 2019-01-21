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
package de.ovgu.featureide.munge_extended;

import java.util.LinkedHashSet;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.munge.MungePreprocessor;

/**
 * Munge Preprocessor adapted for usage with all kind of code projects.
 *
 * Compatibility with the Android Toolkit is achieved by bundling the src and res folders the Android builder expects into the FeatureIDE source folder. The
 * composed files are copied to the project's root folder after every FeatureIDE build. Then they can be processed by the Android builders.
 *
 * @author Nicolas Hlad
 */
public class MungeExtendedPreprocessor extends MungePreprocessor {

	private static final LinkedHashSet<String> EXTENSIONS = new LinkedHashSet<String>();
	static {
		// for Java Projects
		EXTENSIONS.add("java");
		EXTENSIONS.add("xml");

		// for Web Projects
		EXTENSIONS.add("ts");
		EXTENSIONS.add("css");
		// EXTENSIONS.add("json");
		// EXTENSIONS.add("js");
		EXTENSIONS.add("html");
		EXTENSIONS.add("htm");
		EXTENSIONS.add("scss");
	};

	public MungeExtendedPreprocessor() {
		super();
	}

	/**
	 * Cleans the copied src and res folders.
	 */
	@Override
	public boolean clean() {
		try {
			final IProject project = featureProject.getProject();

			final IFolder srcFolder = project.getFolder("src");
			if (srcFolder.exists() && srcFolder.isAccessible()) {
				for (final IResource member : srcFolder.members()) {
					member.delete(false, null);
				}
			}

			final IFolder resFolder = project.getFolder("res");
			if (resFolder.exists() && resFolder.isAccessible()) {
				for (final IResource member : resFolder.members()) {
					member.delete(false, null);
				}
			}
		} catch (final CoreException e) {
			MungeExtendedCorePlugin.getDefault().logError(e);
		}
		return super.clean();
	}

	@Override
	public void copyNotComposedFiles(Configuration c, IFolder destination) {
		final List<IFeature> selectedFeatures = c.getSelectedFeatures();
		if (selectedFeatures != null) {
			if (destination == null) {
				destination = featureProject.getBuildFolder();
			}

			for (final IFeature feature : selectedFeatures) {
				final IFolder folder = featureProject.getSourceFolder().getFolder(feature.getName());
				try {
					if (!destination.exists()) {
						destination.create(false, true, null);
					}
					copy(folder, destination);
				} catch (final CoreException e) {
					CorePlugin.getDefault().logError(e);
				}
			}
		}
	}
	/*
	 * @Override
	 * protected void runMunge(LinkedList<String> featureArgs, IFolder sourceFolder, IFolder buildFolder) {
	 * final LinkedList<String> packageArgs = new LinkedList<String>(featureArgs);
	 * boolean added = false;
	 * try {
	 * createBuildFolder(buildFolder);
	 * for (final IResource res : sourceFolder.members()) {
	 * if (res instanceof IFolder) {
	 * runMunge(featureArgs, (IFolder) res, buildFolder.getFolder(res.getName()));
	 * } else if (res instanceof IFile) {
	 * final String extension = res.getFileExtension();
	 * if ((extension != null) && (isExtensionFileCorrected(extension))) {
	 * added = true;
	 * packageArgs.add(res.getRawLocation().toOSString());
	 * }
	 * }
	 * }
	 * } catch (final CoreException e) {
	 * MungeCorePlugin.getDefault().logError(e);
	 * }
	 * if (!added) {
	 * return;
	 * }
	 * // add output directory
	 * packageArgs.add(buildFolder.getRawLocation().toOSString());
	 * // CommandLine syntax:
	 * // -DFEATURE1 -DFEATURE2 ... File1 File2 ... outputDirectory
	 * runMunge(packageArgs);
	 * }
	 */

	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
	}

	private boolean isExtensionFileCorrected(String fileExtension) {
		// checked all extentions with the parameter fileExtension
		for (final String validExtension : EXTENSIONS) {
			if (fileExtension.equals(validExtension)) {
				return true;
			}
		}
		return false;
	}

}
