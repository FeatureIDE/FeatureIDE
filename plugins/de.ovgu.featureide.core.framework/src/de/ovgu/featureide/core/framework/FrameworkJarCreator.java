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
package de.ovgu.featureide.core.framework;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.net.URL;
import java.util.jar.JarOutputStream;
import java.util.zip.ZipEntry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;

/**
 * Class for adding files or folders to jars
 *
 * @author Daniel Hohmann
 */
public class FrameworkJarCreator {

	/**
	 * Adding given file to jar
	 *
	 * @param jarStream
	 * @param res - file
	 * @param path - String representation for path inside jar
	 * @throws IOException
	 */
	public static void addFileToJar(JarOutputStream jarStream, IFile res, String path) throws IOException {
		jarStream.putNextEntry(new ZipEntry(path + res.getName()));
		final URL location = FileLocator.toFileURL(res.getLocationURI().toURL());
		final File file = new File(location.getPath());
		try (BufferedInputStream in = new BufferedInputStream(new FileInputStream(file))) {
			final byte[] buffer = new byte[1024];
			while (true) {
				final int count = in.read(buffer);
				if (count == -1) {
					break;
				}
				jarStream.write(buffer, 0, count);
			}
		}
		jarStream.closeEntry();
	}

	/**
	 * recursive method caller
	 *
	 * @param jarStream
	 * @param bin
	 * @throws CoreException
	 * @throws IOException
	 */
	public static void addToJar(JarOutputStream jarStream, IResource bin) throws CoreException, IOException {
		if (bin instanceof IFolder) {
			for (final IResource member : ((IFolder) bin).members()) {
				addToJar(jarStream, member, "");
			}
		}
	}

	/**
	 * recursive method<br> calls other methods depending on type (file or folder)
	 *
	 * @param jarStream
	 * @param res
	 * @param path
	 * @throws IOException
	 * @throws CoreException
	 */
	public static void addToJar(JarOutputStream jarStream, IResource res, String path) throws IOException, CoreException {
		if (res instanceof IFolder) {
			final String path2 = path + res.getName() + "/"; // Slash is needed for JAR creation -> DO NOT REPLACE WITH SYSTEM PROPERTIES
			for (final IResource member : ((IFolder) res).members()) {
				addToJar(jarStream, member, path2);
			}
		} else if (res instanceof IFile) {
			addFileToJar(jarStream, (IFile) res, path);
		}
	}
}
