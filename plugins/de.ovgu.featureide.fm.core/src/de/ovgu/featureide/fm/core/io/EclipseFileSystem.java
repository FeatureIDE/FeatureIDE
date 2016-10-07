package de.ovgu.featureide.fm.core.io;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedList;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.fm.core.io.FileSystem.IFileSystem;

public class EclipseFileSystem implements IFileSystem {

	@Override
	public void write(Path path, byte[] content) throws IOException {
		final IFile file = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(getIPath(path));
		if (file == null) {
			throw new IOException(new NullPointerException());
		}
		try {
			if (file.exists()) {
				file.setContents(new ByteArrayInputStream(content), true, true, null);
			} else {
				file.create(new ByteArrayInputStream(content), true, null);
			}
		} catch (CoreException e) {
			throw new IOException(e);
		}
	}

	@Override
	public void append(Path path, byte[] content) throws IOException {
		final IFile file = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(getIPath(path));
		if (file == null) {
			throw new IOException(new NullPointerException());
		}
		try {
			file.appendContents(new ByteArrayInputStream(content), true, true, null);
		} catch (CoreException e) {
			throw new IOException(e);
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
			throw new IOException(new NullPointerException());
		}
		try {
			if (container instanceof IFolder) {
				final LinkedList<IFolder> folders = new LinkedList<>();
				while (!container.exists()) {
					folders.addFirst((IFolder) container);
					container = container.getParent();
				}
				for (IFolder folder : folders) {
					folder.create(true, true, null);
				}
			}
		} catch (CoreException | ClassCastException | NullPointerException e) {
			throw new IOException(e);
		}
	}

	@Override
	public void delete(Path path) throws IOException {
		final IPath iPath = getIPath(path);
		IResource res = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(iPath);
		try {
			if (res != null && res.exists()) {
				res.delete(true, null);
			}
			res = ResourcesPlugin.getWorkspace().getRoot().getContainerForLocation(iPath);
			if (res != null && res.exists()) {
				res.delete(true, null);
			}
		} catch (CoreException e) {
			throw new IOException(e);
		}
	}

	@Override
	public boolean exists(Path path) {
		final IPath iPath = getIPath(path);
		IResource res = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(iPath);
		if (res != null && res.isAccessible()) {
			return true;
		}
		res = ResourcesPlugin.getWorkspace().getRoot().getContainerForLocation(iPath);
		return res != null && res.isAccessible();
	}

	private IPath getIPath(Path path) {
		return org.eclipse.core.runtime.Path.fromOSString(path.toAbsolutePath().toString());
	}

}
