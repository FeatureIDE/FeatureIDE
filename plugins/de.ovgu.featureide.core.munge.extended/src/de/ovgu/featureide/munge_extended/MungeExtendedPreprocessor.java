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

import java.io.File;
import java.io.IOException;
import java.util.LinkedHashSet;
import java.util.LinkedList;

import org.apache.commons.io.FileUtils;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.sonatype.plugins.munge.Munge;

import de.ovgu.featureide.munge.MungeCorePlugin;
import de.ovgu.featureide.munge.MungePreprocessor;

/**
 * Munge Preprocessor adapted for usage with all kind of code projects.
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
	protected void runMunge(LinkedList<String> featureArgs, IFolder sourceFolder, IFolder buildFolder) {
		final LinkedList<String> packageArgs = new LinkedList<String>(featureArgs);
		boolean added = false;
		try {
			createBuildFolder(buildFolder);
			for (final IResource res : sourceFolder.members()) {
				if (res instanceof IFolder) {
					runMunge(featureArgs, (IFolder) res, buildFolder.getFolder(res.getName()));
				} else if (res instanceof IFile) {
					final String extension = res.getFileExtension();
					if ((extension != null) && (isExtensionFileCorrected(extension))) {
						added = true;
						packageArgs.add(res.getRawLocation().toOSString());
					} else {
						added = false;
						final File source = new File(res.getRawLocation().toOSString());
						final File dest = new File(buildFolder.getRawLocation().toOSString());
						try {
							FileUtils.copyFileToDirectory(source, dest);
						} catch (final IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
				}
			}
		} catch (final CoreException e) {
			MungeCorePlugin.getDefault().logError(e);
		}
		if (!added) {
			return;
		}
		// add output directory
		packageArgs.add(buildFolder.getRawLocation().toOSString());
		// CommandLine syntax:
		// -DFEATURE1 -DFEATURE2 ... File1 File2 ... outputDirectory
		runMunge(packageArgs);
	}

	@Override
	protected void runMunge(LinkedList<String> args) {
		// run Munge
		final Munge m = new Munge();
		m.main(args.toArray(new String[0]), featureProject);
	}

	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
	}

}
