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
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.JavaConventions;
import org.eclipse.jdt.core.JavaCore;

import de.ovgu.featureide.ui.UIPlugin;

/**
 * A place for new Java packages and classes in a feature: a source folder (the feature folder or its <code>src/main/java</code>) and a package in it.
 *
 * @author Philipp Hehnle
 */
public final class FeatureJavaLocation {

	private static final String JAVA_SOURCE_FOLDER = "src/main/java";

	private final IFolder featureFolder;
	private final IContainer root;
	private final String packageName;

	public FeatureJavaLocation(IFolder featureFolder, IContainer root, String packageName) {
		this.featureFolder = featureFolder;
		this.root = root;
		this.packageName = packageName;
	}

	/**
	 * Determines the location for new Java elements from a selected element.
	 *
	 * @param element a feature folder, {@link FeaturePackageRoot}, {@link FeaturePackage}, or a resource in a feature folder.
	 * @return the location, or <code>null</code> if the element is not in a feature folder whose content is shown as packages.
	 */
	public static FeatureJavaLocation of(Object element) {
		if (element instanceof FeaturePackage) {
			final FeaturePackage featurePackage = (FeaturePackage) element;
			final IFolder featureFolder = FeatureFolders.getFeatureFolder(featurePackage.getRoot());
			return (featureFolder == null) ? null
				: new FeatureJavaLocation(featureFolder, featurePackage.getRoot(), featurePackage.isDefaultPackage() ? "" : featurePackage.getName());
		} else if (element instanceof FeaturePackageRoot) {
			final FeaturePackageRoot root = (FeaturePackageRoot) element;
			return new FeatureJavaLocation(root.getFeatureFolder(), root.getFolder(), "");
		} else if (element instanceof IResource) {
			final IResource resource = (IResource) element;
			final IFolder featureFolder = FeatureFolders.getFeatureFolder(resource);
			if (featureFolder == null) {
				return null;
			}
			final IContainer root = getJavaSourceFolder(featureFolder);
			final IContainer container = (resource instanceof IContainer) ? (IContainer) resource : resource.getParent();
			return new FeatureJavaLocation(featureFolder, root, getPackageName(root, container));
		}
		return null;
	}

	/**
	 * @return <code>src/main/java</code> if the feature folder uses the Maven layout, otherwise the feature folder itself.
	 */
	private static IContainer getJavaSourceFolder(IFolder featureFolder) {
		return FeaturePackageStructure.getSourceFolders(featureFolder).isEmpty() ? featureFolder : featureFolder.getFolder(JAVA_SOURCE_FOLDER);
	}

	/**
	 * @return the name of the package that the container is (or is in), or "" if it is not in a package below the root.
	 */
	private static String getPackageName(IContainer root, IContainer container) {
		if (!root.getFullPath().isPrefixOf(container.getFullPath())) {
			return "";
		}
		final String[] segments = container.getFullPath().makeRelativeTo(root.getFullPath()).segments();
		final StringBuilder name = new StringBuilder();
		for (final String segment : segments) {
			if (!isValidPackageName(segment) || segment.contains(".")) {
				break;
			}
			if (name.length() > 0) {
				name.append('.');
			}
			name.append(segment);
		}
		return name.toString();
	}

	public IFolder getFeatureFolder() {
		return featureFolder;
	}

	/**
	 * @return the source folder the package names are relative to.
	 */
	public IContainer getRoot() {
		return root;
	}

	/**
	 * @return the package name, or "" for the default package.
	 */
	public String getPackageName() {
		return packageName;
	}

	/**
	 * @return the folder of the given package in the source folder.
	 */
	public IContainer getPackageFolder(String packageName) {
		return packageName.isEmpty() ? root : root.getFolder(new Path(packageName.replace('.', '/')));
	}

	/**
	 * Creates the folders of the given package, if they do not exist yet. Also creates the source folder (e.g. <code>src/main/java</code>) if needed.
	 *
	 * @return the folder of the package.
	 */
	public IContainer createPackage(String packageName) throws CoreException {
		final IContainer folder = getPackageFolder(packageName);
		createFolder(folder);
		return folder;
	}

	private static void createFolder(IContainer container) throws CoreException {
		if ((container instanceof IFolder) && !container.exists()) {
			createFolder(container.getParent());
			((IFolder) container).create(true, true, null);
		}
	}

	/**
	 * @return the node that shows the given package in the Project Explorer.
	 */
	public FeaturePackage getPackageNode(String packageName) {
		final Object parent = root.equals(featureFolder) ? featureFolder : new FeaturePackageRoot((IFolder) root, featureFolder);
		return new FeaturePackage(parent, root, getPackageFolder(packageName));
	}

	/**
	 * @return a description of the source folder, e.g. <code>Project/features/Base</code> or <code>Project/features/Base/src/main/java</code>.
	 */
	public String getRootLabel() {
		return root.getFullPath().makeRelative().toString();
	}

	/**
	 * Validates a package name like the New Package wizard of JDT.
	 *
	 * @param packageName the package name. The empty name (default package) is valid if <code>allowDefaultPackage</code> is set.
	 * @return an OK, warning (e.g. for upper case names) or error status.
	 */
	public static IStatus validatePackageName(String packageName, boolean allowDefaultPackage) {
		if (packageName.isEmpty()) {
			return allowDefaultPackage ? Status.OK_STATUS : new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Package name is empty.");
		}
		return JavaConventions.validatePackageName(packageName, JavaCore.VERSION_21, JavaCore.VERSION_21);
	}

	/**
	 * Validates a type name like the New Class wizard of JDT.
	 */
	public static IStatus validateTypeName(String typeName) {
		if (typeName.isEmpty()) {
			return new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Type name is empty.");
		}
		if (typeName.contains(".")) {
			return new Status(IStatus.ERROR, UIPlugin.PLUGIN_ID, "Type name must not be qualified.");
		}
		return JavaConventions.validateJavaTypeName(typeName, JavaCore.VERSION_21, JavaCore.VERSION_21);
	}

	private static boolean isValidPackageName(String segment) {
		return validatePackageName(segment, false).getSeverity() != IStatus.ERROR;
	}
}
