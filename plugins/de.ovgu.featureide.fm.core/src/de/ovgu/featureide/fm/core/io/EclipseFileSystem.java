/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.net.URI;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedList;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.io.FileSystem.IFileSystem;

public class EclipseFileSystem implements IFileSystem {

	public static IPath getIPath(Path path) {
		return path == null ? null : org.eclipse.core.runtime.Path.fromOSString(path.toAbsolutePath().toString());
	}

	public static IResource getResource(Path path) {
		if ((path != null) && Files.exists(path)) {
			final IPath iPath = getIPath(path);
			if (iPath != null) {
				final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
				return Files.isDirectory(path) ? root.getContainerForLocation(iPath) : root.getFileForLocation(iPath);
			}
		}
		return null;
	}

	public static final Path getPath(IResource res) {
		if (res != null) {
			final URI locationURI = res.getLocationURI();
			if (locationURI != null) {
				return Paths.get(locationURI);
			}
		}
		return null;
	}

	private final JavaFileSystem JAVA = new JavaFileSystem();

	@Override
	public void write(Path path, byte[] content) throws IOException {
		final IFile file = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(getIPath(path));
		if (file == null) {
			JAVA.write(path, content);
		} else {
			try {
				if (file.exists()) {
					file.deleteMarkers(null, true, IResource.DEPTH_ZERO);
					file.setContents(new ByteArrayInputStream(content), true, false, null);
				} else {
					file.create(new ByteArrayInputStream(content), true, null);
				}
			} catch (final CoreException e) {
				throw new IOException(e);
			}
		}
	}

	@Override
	public void append(Path path, byte[] content) throws IOException {
		final IFile file = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(getIPath(path));
		if (file == null) {
			JAVA.append(path, content);
		} else {
			try {
				file.appendContents(new ByteArrayInputStream(content), true, true, null);
			} catch (final CoreException e) {
				throw new IOException(e);
			}
		}
	}

	@Override
	public byte[] read(Path path) throws IOException {
		return Files.readAllBytes(path);
	}

	@Override
	public void mkDir(Path path) throws IOException {
		IContainer container = ResourcesPlugin.getWorkspace().getRoot().getContainerForLocation(getIPath(path));
		if (container == null) {
			JAVA.mkDir(path);
		} else {
			try {
				if (container instanceof IFolder) {
					final LinkedList<IFolder> folders = new LinkedList<>();
					while (!container.exists()) {
						folders.addFirst((IFolder) container);
						container = container.getParent();
					}
					for (final IFolder folder : folders) {
						folder.create(true, true, null);
					}
				}
			} catch (CoreException | ClassCastException | NullPointerException e) {
				throw new IOException(e);
			}
		}
	}

	@Override
	public void delete(Path path) throws IOException {
		final IResource res = getResource(path);
		try {
			if (res == null) {
				JAVA.exists(path);
			} else if (res.exists()) {
				res.delete(true, null);
			}
		} catch (final CoreException e) {
			throw new IOException(e);
		}
	}

	@Override
	public boolean exists(Path path) {
		final IResource res = getResource(path);
		if (res == null) {
			return JAVA.exists(path);
		} else {
			return res.isAccessible();
		}
	}

	@Override
	public Path getLib(Path path) {
		URL url = FileLocator.find(FMCorePlugin.getDefault().getBundle(), new org.eclipse.core.runtime.Path("lib/cover.exe"), null);
		try {
			url = FileLocator.toFileURL(url);
			return Paths.get(url.getPath().substring(1)).normalize();
		} catch (final IOException e) {
			Logger.logError(e);
			return null;
		}
	}

}
