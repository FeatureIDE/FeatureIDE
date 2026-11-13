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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.JavaConventions;
import org.eclipse.jdt.core.JavaCore;

/**
 * Computes the package structure of a feature folder, independent of any viewer.
 * <p>
 * A feature folder is shown like a Java source folder: every folder that contains files is a package, named by its path relative to the feature folder,
 * e.g. <code>de.ovgu.example</code> for <code>de/ovgu/example</code>. As in the Package Explorer, folders whose names are not valid package names (e.g.
 * <code>de.ovgu</code> or <code>META-INF</code>) are no packages and are shown as normal folders, together with their content.
 * <p>
 * If the feature folder uses the Maven layout, its source folders are shown as {@link FeaturePackageRoot source folders} that contain the packages instead.
 * Depending on the target folder of the project (e.g. <code>src</code> or <code>src/main</code> instead of <code>src/main/java</code>), the feature folders
 * contain the Maven source folders on different levels, see {@link #SOURCE_FOLDERS}: e.g. <code>src/main/java</code>, <code>main/java</code> or
 * <code>java</code>, and the same for <code>test</code> and <code>resources</code>. The folders above the source folders (e.g. <code>src</code>,
 * <code>main</code> or <code>test</code>) are not shown as packages, and not shown at all if they only contain source folders. Only the content of the
 * Java source folders (e.g. <code>src/main/java</code>) is shown as packages; the content of the resource folders (e.g. <code>main/resources</code>) is
 * shown as normal folders and files.
 *
 * @author Philipp Hehnle
 */
public final class FeaturePackageStructure {

	/**
	 * Source folders inside a feature folder that are shown as {@link FeaturePackageRoot}s, relative to the feature folder. They cover the Maven layout for
	 * the different target folders of a project:
	 * <ul>
	 * <li>the project folder as target: the feature folders contain <code>src/main/java</code>, <code>src/test/java</code>, ...</li>
	 * <li><code>src</code> as target: the feature folders contain <code>main/java</code>, <code>test/java</code>, ...</li>
	 * <li><code>src/main</code> as target: the feature folders contain <code>java</code> and <code>resources</code>.</li>
	 * </ul>
	 * The Java source folders come first, the main ones before the test ones and the higher levels before the lower ones; see
	 * {@link #getJavaSourceFolder(IFolder)}.
	 */
	public static final List<IPath> SOURCE_FOLDERS = List.of( //
			new Path("src/main/java"), new Path("main/java"), new Path("java"), //
			new Path("src/test/java"), new Path("test/java"), //
			new Path("src/main/resources"), new Path("main/resources"), new Path("resources"), //
			new Path("src/test/resources"), new Path("test/resources"));

	/**
	 * The name of Java source folders, e.g. <code>src/main/java</code> or <code>test/java</code>.
	 */
	private static final String JAVA_FOLDER_NAME = "java";

	/**
	 * The name of the folder that contains the test source folders, e.g. <code>src/test</code> or <code>test</code>.
	 */
	private static final String TEST_FOLDER_NAME = "test";

	/**
	 * Files with these extensions in the root of a source folder belong to the default package. Other files are shown directly in the source folder.
	 */
	private static final Set<String> SOURCE_FILE_EXTENSIONS = Set.of("java", "jak");

	private FeaturePackageStructure() {}

	/**
	 * @return the existing {@link #SOURCE_FOLDERS} of the feature folder.
	 */
	public static List<FeaturePackageRoot> getSourceFolders(IFolder featureFolder) {
		final List<FeaturePackageRoot> roots = new ArrayList<>();
		for (final IPath path : SOURCE_FOLDERS) {
			final IFolder folder = featureFolder.getFolder(path);
			if (folder.exists()) {
				roots.add(new FeaturePackageRoot(folder, featureFolder));
			}
		}
		return roots;
	}

	/**
	 * @return the source folder of the feature folder that contains the given resource (or is the resource), or <code>null</code> if the resource is not in
	 *         a source folder.
	 */
	public static FeaturePackageRoot getSourceFolder(IResource resource, IFolder featureFolder) {
		for (final FeaturePackageRoot root : getSourceFolders(featureFolder)) {
			if (root.getFolder().getFullPath().isPrefixOf(resource.getFullPath())) {
				return root;
			}
		}
		return null;
	}

	/**
	 * @return whether the source folder contains Java sources (e.g. <code>src/main/java</code> or <code>test/java</code>), not resources.
	 */
	public static boolean isJavaSourceFolder(FeaturePackageRoot root) {
		return JAVA_FOLDER_NAME.equals(root.getFolder().getName());
	}

	/**
	 * Determines the folder for new Java packages and classes that are not created in a specific source folder.
	 *
	 * @return the feature folder, if it does not use the Maven layout. Otherwise the existing main Java source folder (e.g. <code>main/java</code>). If it
	 *         does not exist yet, the main Java source folder on the level of the existing source folders, e.g. <code>main/java</code> if the feature folder
	 *         only contains <code>main/resources</code> or <code>test/java</code>.
	 */
	public static IContainer getJavaSourceFolder(IFolder featureFolder) {
		final List<FeaturePackageRoot> roots = getSourceFolders(featureFolder);
		if (roots.isEmpty()) {
			return featureFolder;
		}
		final FeaturePackageRoot first = roots.get(0);
		if (isJavaSourceFolder(first) && !isTestSourceFolder(first)) {
			return first.getFolder();
		}
		final int level = first.getFolder().getFullPath().segmentCount() - featureFolder.getFullPath().segmentCount();
		for (final IPath path : SOURCE_FOLDERS) {
			if (path.segmentCount() == level) {
				// the first source folder on each level is the main Java source folder
				return featureFolder.getFolder(path);
			}
		}
		return featureFolder.getFolder(SOURCE_FOLDERS.get(0));
	}

	/**
	 * @return whether the source folder contains tests, e.g. <code>src/test/java</code> or <code>test/resources</code>.
	 */
	private static boolean isTestSourceFolder(FeaturePackageRoot root) {
		final IPath path = root.getFolder().getFullPath().makeRelativeTo(root.getFeatureFolder().getFullPath());
		return (path.segmentCount() >= 2) && TEST_FOLDER_NAME.equals(path.segment(path.segmentCount() - 2));
	}

	/**
	 * @return the nodes to show in the feature folder: either its {@link FeaturePackageRoot source folders} and its other resources, or its packages.
	 */
	public static List<Object> getFeatureFolderChildren(IFolder featureFolder) throws CoreException {
		final List<FeaturePackageRoot> roots = getSourceFolders(featureFolder);
		if (roots.isEmpty()) {
			return getPackageRootChildren(featureFolder, featureFolder);
		}
		final List<Object> children = new ArrayList<>(roots);
		for (final IResource member : featureFolder.members()) {
			if (!isCoveredBySourceFolders(member, roots)) {
				children.add(member);
			}
		}
		return children;
	}

	/**
	 * Removes the resources that are already shown through a {@link FeaturePackageRoot}. This is needed for the children of the folders <code>src</code> and
	 * <code>src/main</code>, if they also contain other resources (e.g. <code>src/test</code>) and are therefore still shown as folders.
	 *
	 * @param featureFolder the feature folder containing the resources.
	 * @param children the children to filter; modified in place.
	 */
	public static void removeResourcesInSourceFolders(IFolder featureFolder, Collection<Object> children) {
		final List<FeaturePackageRoot> roots = getSourceFolders(featureFolder);
		if (!roots.isEmpty()) {
			children.removeIf(child -> (child instanceof IResource) && isCoveredBySourceFolders((IResource) child, roots));
		}
	}

	/**
	 * @return the nodes to show in the source folder: packages for Java source folders, the normal folders and files for resource folders.
	 */
	public static List<Object> getSourceFolderChildren(FeaturePackageRoot root) throws CoreException {
		if (isJavaSourceFolder(root)) {
			return getPackageRootChildren(root, root.getFolder());
		}
		return new ArrayList<>(List.of(root.getFolder().members()));
	}

	/**
	 * @param parent the node to show the children in: the feature folder or the {@link FeaturePackageRoot}.
	 * @param root the folder of the package root: the feature folder or the folder of the {@link FeaturePackageRoot}.
	 * @return the default package (if it contains source files), the other files in the root, all packages below the root, and the folders in the root
	 *         whose names are not valid package names.
	 */
	public static List<Object> getPackageRootChildren(Object parent, IContainer root) throws CoreException {
		final List<Object> children = new ArrayList<>();
		boolean hasSourceFiles = false;
		for (final IResource member : root.members()) {
			if (member instanceof IFile) {
				if (isSourceFile((IFile) member)) {
					hasSourceFiles = true;
				} else {
					children.add(member);
				}
			} else if ((member instanceof IFolder) && !isPackageFolder(member)) {
				children.add(member);
			}
		}
		if (hasSourceFiles) {
			children.add(new FeaturePackage(parent, root, root));
		}
		collectPackages(parent, root, root, children);
		return children;
	}

	/**
	 * Adds a package for every folder below the given container whose name is a valid package name and that contains files (or folders that are not
	 * packages) or is empty. As in the Package Explorer, folders that only contain other packages are not shown. Folders whose names are not valid package
	 * names (e.g. <code>de.ovgu</code> or <code>META-INF</code>) are not packages, neither is their content; they are shown as normal folders.
	 */
	private static void collectPackages(Object parent, IContainer root, IContainer container, List<Object> packages) throws CoreException {
		for (final IResource member : container.members()) {
			if ((member instanceof IFolder) && isPackageFolder(member)) {
				final IFolder folder = (IFolder) member;
				boolean hasContent = false;
				boolean hasSubpackages = false;
				for (final IResource child : folder.members()) {
					if ((child instanceof IFile) || ((child instanceof IFolder) && !isPackageFolder(child))) {
						hasContent = true;
					} else if (child instanceof IFolder) {
						hasSubpackages = true;
					}
				}
				if (hasContent || !hasSubpackages) {
					packages.add(new FeaturePackage(parent, root, folder));
				}
				collectPackages(parent, root, folder, packages);
			}
		}
	}

	/**
	 * @return the files of the package and its folders that are not packages. Subfolders with valid package names are separate packages. The default package
	 *         only contains the source files of the root.
	 */
	public static List<IResource> getPackageChildren(FeaturePackage featurePackage) throws CoreException {
		final List<IResource> children = new ArrayList<>();
		for (final IResource member : featurePackage.getFolder().members()) {
			if (featurePackage.isDefaultPackage()) {
				if ((member instanceof IFile) && isSourceFile((IFile) member)) {
					children.add(member);
				}
			} else if ((member instanceof IFile) || ((member instanceof IFolder) && !isPackageFolder(member))) {
				children.add(member);
			}
		}
		return children;
	}

	/**
	 * @return whether the name of the folder is a valid package name segment, as in the Package Explorer. For example, <code>de.ovgu</code> is not: the
	 *         package <code>de.ovgu</code> is the folder <code>de/ovgu</code>.
	 */
	public static boolean isPackageFolder(IResource folder) {
		final String name = folder.getName();
		return (name.indexOf('.') < 0)
			&& (JavaConventions.validatePackageName(name, JavaCore.VERSION_21, JavaCore.VERSION_21).getSeverity() != IStatus.ERROR);
	}

	/**
	 * @return the node in which the given resource below the feature folder is shown, or <code>null</code> if it is shown in its usual parent folder.
	 */
	public static Object getParent(IResource resource, IFolder featureFolder) {
		final List<FeaturePackageRoot> roots = getSourceFolders(featureFolder);
		if (roots.isEmpty()) {
			return getParentInPackageRoot(resource, featureFolder, featureFolder);
		}
		for (final FeaturePackageRoot root : roots) {
			if (root.getFolder().getFullPath().isPrefixOf(resource.getFullPath()) && !root.getFolder().equals(resource)) {
				if (!isJavaSourceFolder(root)) {
					// resource folders show their content as normal folders and files
					return root.getFolder().equals(resource.getParent()) ? root : null;
				}
				return getParentInPackageRoot(resource, root, root.getFolder());
			}
		}
		if (roots.stream().anyMatch(root -> root.getFolder().equals(resource))) {
			return featureFolder;
		}
		return null;
	}

	private static Object getParentInPackageRoot(IResource resource, Object rootNode, IContainer root) {
		final IContainer container = resource.getParent();
		if (isInNonPackageFolder(container, root)) {
			// the content of folders that are not packages is shown in these folders
			return container;
		}
		if ((resource instanceof IFolder) && isPackageFolder(resource)) {
			// packages are shown directly in the root
			return rootNode;
		}
		if (container.equals(root)) {
			return ((resource instanceof IFile) && isSourceFile((IFile) resource)) ? new FeaturePackage(rootNode, root, root) : rootNode;
		}
		return new FeaturePackage(rootNode, root, container);
	}

	/**
	 * @return whether the container or one of its parent folders below the root is not a package folder.
	 */
	private static boolean isInNonPackageFolder(IContainer container, IContainer root) {
		for (IContainer current = container; (current != null) && !current.equals(root); current = current.getParent()) {
			if (!isPackageFolder(current)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @return whether the resource is one of the source folders, or a folder (like <code>src</code>) that only contains source folders.
	 */
	private static boolean isCoveredBySourceFolders(IResource resource, List<FeaturePackageRoot> roots) {
		if (!(resource instanceof IFolder)) {
			return false;
		}
		for (final FeaturePackageRoot root : roots) {
			if (root.getFolder().equals(resource)) {
				return true;
			}
		}
		boolean containsSourceFolder = false;
		for (final FeaturePackageRoot root : roots) {
			if (resource.getFullPath().isPrefixOf(root.getFolder().getFullPath())) {
				containsSourceFolder = true;
			}
		}
		if (!containsSourceFolder) {
			return false;
		}
		try {
			for (final IResource member : ((IFolder) resource).members()) {
				if (!isCoveredBySourceFolders(member, roots)) {
					return false;
				}
			}
		} catch (final CoreException e) {
			return false;
		}
		return true;
	}

	private static boolean isSourceFile(IFile file) {
		final String extension = file.getFileExtension();
		return (extension != null) && SOURCE_FILE_EXTENSIONS.contains(extension);
	}
}
