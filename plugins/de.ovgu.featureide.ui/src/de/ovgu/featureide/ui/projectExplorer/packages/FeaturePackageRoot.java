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
package de.ovgu.featureide.ui.projectExplorer.packages;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;

/**
 * A source folder inside a feature folder, such as <code>src/main/java</code> or <code>src/main/resources</code>. It is shown as one node, like a Maven
 * source folder in a Java project, and contains packages.
 *
 * @author Philipp Hehnle
 */
public final class FeaturePackageRoot implements IAdaptable {

	private final IFolder folder;
	private final IFolder featureFolder;

	public FeaturePackageRoot(IFolder folder, IFolder featureFolder) {
		this.folder = folder;
		this.featureFolder = featureFolder;
	}

	/**
	 * @return the folder of this source folder, e.g. <code>Feature/src/main/java</code>.
	 */
	public IFolder getFolder() {
		return folder;
	}

	/**
	 * @return the feature folder this source folder belongs to.
	 */
	public IFolder getFeatureFolder() {
		return featureFolder;
	}

	/**
	 * @return the path relative to the feature folder, e.g. <code>src/main/java</code>.
	 */
	public String getLabel() {
		return folder.getFullPath().makeRelativeTo(featureFolder.getFullPath()).toString();
	}

	@Override
	public <T> T getAdapter(Class<T> adapter) {
		if ((adapter == IResource.class) || (adapter == IContainer.class) || (adapter == IFolder.class)) {
			return adapter.cast(folder);
		}
		return null;
	}

	@Override
	public boolean equals(Object obj) {
		return (obj instanceof FeaturePackageRoot) && folder.equals(((FeaturePackageRoot) obj).folder);
	}

	@Override
	public int hashCode() {
		return folder.hashCode();
	}

	@Override
	public String toString() {
		return getLabel();
	}
}
