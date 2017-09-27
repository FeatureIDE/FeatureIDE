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
package de.ovgu.featureide.fm.core.io.manager;

import java.net.URI;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.fm.core.Logger;

/**
 * Responsible to load and save all information from / to a file.</br> To get an instance use the {@link FileManagerMap}.
 *
 * @author Sebastian Krieter
 */
@Deprecated
public abstract class FileListener<T> implements IResourceChangeListener {

	private final AFileManager<T> fileManager;

	private final IPath eclipseFile;

	protected FileListener(AFileManager<T> fileManager) {
		this.fileManager = fileManager;
		IPath absolutePath2 = new org.eclipse.core.runtime.Path(fileManager.getAbsolutePath());
		final IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		final IPath rootLocation = root.getLocation();
		if (absolutePath2.matchingFirstSegments(rootLocation) != rootLocation.segmentCount()) {
			try {
				final IFile[] filesOfLocation = root.findFilesForLocationURI(URI.create("file:/" + absolutePath2.toString().replace(" ", "%20")));
				absolutePath2 = filesOfLocation[0].getFullPath().makeRelativeTo(rootLocation);
			} catch (final IndexOutOfBoundsException e) {
				Logger.logError(e);
				eclipseFile = null;
				return;
			}
		}
		this.eclipseFile = absolutePath2.makeRelativeTo(rootLocation);
	}

	@Override
	public void resourceChanged(IResourceChangeEvent event) {
		if (event.getType() == IResourceChangeEvent.POST_CHANGE) {
			final IResourceDelta delta = event.getDelta();
			if (delta != null) {
				final IResourceDelta deltaMember = delta.findMember(eclipseFile);
				if (deltaMember != null) {
					final IResourceDeltaVisitor visitor = new IResourceDeltaVisitor() {

						@Override
						public boolean visit(IResourceDelta delta) {
							if ((delta.getKind() == IResourceDelta.CHANGED) && ((delta.getFlags() & IResourceDelta.CONTENT) != 0)) {
								fileManager.read();
							}
							return true;
						}
					};
					try {
						deltaMember.accept(visitor);
					} catch (final CoreException e) {}
				}
			}
		}
	}

	@Override
	public String toString() {
		return "Resource change listener for " + fileManager.getAbsolutePath();
	}

}
