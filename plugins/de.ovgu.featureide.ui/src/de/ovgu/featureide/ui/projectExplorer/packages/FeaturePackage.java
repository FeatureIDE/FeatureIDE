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
 * A package inside a feature folder, shown like a package of a Java source folder, e.g. <code>de.ovgu.example</code> for the folder
 * <code>Feature/de/ovgu/example</code>.
 *
 * @author Philipp Hehnle
 */
public final class FeaturePackage implements IAdaptable {

	/**
	 * Name of the default package, as in the Package Explorer.
	 */
	public static final String DEFAULT_PACKAGE_NAME = "(default package)";

	private final Object parent;
	private final IContainer root;
	private final IContainer folder;

	/**
	 * @param parent the node the package is shown in: the feature folder or a {@link FeaturePackageRoot}.
	 * @param root the folder the package names are relative to: the feature folder or the folder of the {@link FeaturePackageRoot}.
	 * @param folder the folder of the package. For the default package, this is the root itself.
	 */
	public FeaturePackage(Object parent, IContainer root, IContainer folder) {
		this.parent = parent;
		this.root = root;
		this.folder = folder;
	}

	/**
	 * @return the node the package is shown in: the feature folder ({@link IFolder}) or a {@link FeaturePackageRoot}.
	 */
	public Object getParent() {
		return parent;
	}

	public IContainer getRoot() {
		return root;
	}

	public IContainer getFolder() {
		return folder;
	}

	public boolean isDefaultPackage() {
		return folder.equals(root);
	}

	/**
	 * @return the package name, e.g. <code>de.ovgu.example</code>, or {@link #DEFAULT_PACKAGE_NAME}.
	 */
	public String getName() {
		if (isDefaultPackage()) {
			return DEFAULT_PACKAGE_NAME;
		}
		return String.join(".", folder.getFullPath().makeRelativeTo(root.getFullPath()).segments());
	}

	/**
	 * Adapts to the folder of the package, so that the usual resource actions (e.g. new file, refresh) work on it. The default package does not adapt to a
	 * resource, because its folder is the root folder, and actions like delete would affect the whole root.
	 */
	@Override
	public <T> T getAdapter(Class<T> adapter) {
		if (isDefaultPackage()) {
			return null;
		}
		if ((adapter == IResource.class) || (adapter == IContainer.class) || ((adapter == IFolder.class) && (folder instanceof IFolder))) {
			return adapter.cast(folder);
		}
		return null;
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof FeaturePackage)) {
			return false;
		}
		final FeaturePackage other = (FeaturePackage) obj;
		return root.equals(other.root) && folder.equals(other.folder);
	}

	@Override
	public int hashCode() {
		return (31 * root.hashCode()) + folder.hashCode();
	}

	@Override
	public String toString() {
		return getName();
	}
}
