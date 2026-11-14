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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * Tests the package structure that the Project Explorer shows for feature folders.
 *
 * @author Philipp Hehnle
 */
public class TFeaturePackageStructure {

	private IProject project;
	private IFolder feature;

	@Before
	public void createProject() throws CoreException {
		project = ResourcesPlugin.getWorkspace().getRoot().getProject("TFeaturePackageStructure");
		if (project.exists()) {
			project.delete(true, true, null);
		}
		project.create(null);
		project.open(null);
		feature = project.getFolder("features/Base");
	}

	@After
	public void deleteProject() throws CoreException {
		project.delete(true, true, null);
	}

	@Test
	public void featureFolderIsShownAsPackages() throws CoreException {
		createFile(feature, "Main.java");
		createFile(feature, "readme.txt");
		createFile(feature, "de/ovgu/a/A.java");
		createFolder(feature, "de/ovgu/b");
		createFile(feature, "de/other/x/X.java");
		createFile(feature, "de/other/x/data.xml");

		final List<Object> children = FeaturePackageStructure.getFeatureFolderChildren(feature);

		// folders that only contain other folders (de, de.ovgu, de.other) are not packages
		assertEquals(Set.of("readme.txt", "(default package)", "de.ovgu.a", "de.ovgu.b", "de.other.x"), labels(children));
		for (final Object child : children) {
			if (child instanceof FeaturePackage) {
				assertEquals(feature, ((FeaturePackage) child).getParent());
			}
		}
	}

	@Test
	public void packageContainsItsFiles() throws CoreException {
		createFile(feature, "Main.java");
		createFile(feature, "readme.txt");
		createFile(feature, "de/other/x/X.java");
		createFile(feature, "de/other/x/data.xml");
		createFile(feature, "de/other/x/sub/Y.java");

		assertEquals(Set.of("X.java", "data.xml"), labels(FeaturePackageStructure.getPackageChildren(new FeaturePackage(feature, feature, feature.getFolder("de/other/x")))));
		// the default package only contains the source files of the feature folder
		assertEquals(Set.of("Main.java"), labels(FeaturePackageStructure.getPackageChildren(new FeaturePackage(feature, feature, feature))));
	}

	@Test
	public void foldersWithInvalidPackageNamesAreNoPackages() throws CoreException {
		// a single folder named "de.hehnle.test" is not the package de.hehnle.test (that would be de/hehnle/test)
		final IFile test = createFile(feature, "de.hehnle.test/Test.java");
		createFile(feature, "de.hehnle.test/sub/Other.java");
		createFile(feature, "de/my-dir/x.txt");
		createFile(feature, "de/ovgu/A.java");

		final List<Object> children = FeaturePackageStructure.getFeatureFolderChildren(feature);
		assertTrue(children.contains(feature.getFolder("de.hehnle.test")));
		// de is a package, because it contains the folder my-dir, which is not a package
		assertEquals(Set.of("de.hehnle.test", "de", "de.ovgu"), labels(children));
		assertEquals(1, children.stream().filter(child -> child instanceof IFolder).count());

		final FeaturePackage de = new FeaturePackage(feature, feature, feature.getFolder("de"));
		assertEquals(List.of(feature.getFolder("de/my-dir")), FeaturePackageStructure.getPackageChildren(de));

		// the content of folders that are not packages is shown in these folders
		assertEquals(feature.getFolder("de.hehnle.test"), FeaturePackageStructure.getParent(test, feature));
		assertEquals(feature.getFolder("de.hehnle.test"), FeaturePackageStructure.getParent(feature.getFolder("de.hehnle.test/sub"), feature));
		assertEquals(feature, FeaturePackageStructure.getParent(feature.getFolder("de.hehnle.test"), feature));
		assertEquals(de, FeaturePackageStructure.getParent(feature.getFolder("de/my-dir"), feature));
	}

	@Test
	public void resourceFoldersShowNormalFolders() throws CoreException {
		createFile(feature, "src/main/resources/META-INF/MANIFEST.MF");
		final IFile properties = createFile(feature, "src/main/resources/de/ovgu/config/app.properties");
		final IFile root = createFile(feature, "src/main/resources/log.xml");

		final FeaturePackageRoot resources = new FeaturePackageRoot(feature.getFolder("src/main/resources"), feature);
		final List<Object> children = FeaturePackageStructure.getSourceFolderChildren(resources);
		// no packages (like de.ovgu.config), only the folders and files of the resource folder
		assertEquals(List.of(), children.stream().filter(child -> !(child instanceof IResource)).toList());
		assertEquals(Set.of("META-INF", "de", "log.xml"), labels(children));

		// the content of resource folders keeps its usual parent, except for the direct children
		assertEquals(resources, FeaturePackageStructure.getParent(root, feature));
		assertEquals(resources, FeaturePackageStructure.getParent(feature.getFolder("src/main/resources/de"), feature));
		assertNull(FeaturePackageStructure.getParent(properties, feature));
		assertNull(FeaturePackageStructure.getParent(feature.getFolder("src/main/resources/de/ovgu"), feature));
	}

	@Test
	public void mavenSourceFoldersAreShownAsOneNode() throws CoreException {
		createFile(feature, "src/main/java/de/ovgu/a/A.java");
		createFile(feature, "src/main/java/Main.java");
		createFile(feature, "src/main/resources/config/app.properties");
		createFile(feature, "pom.xml");

		final List<Object> children = FeaturePackageStructure.getFeatureFolderChildren(feature);

		// src and src/main are not shown, neither as folders nor as packages
		assertEquals(Set.of("src/main/java", "src/main/resources", "pom.xml"), labels(children));

		final FeaturePackageRoot java = new FeaturePackageRoot(feature.getFolder("src/main/java"), feature);
		final List<Object> javaChildren = FeaturePackageStructure.getPackageRootChildren(java, java.getFolder());
		assertEquals(Set.of("(default package)", "de.ovgu.a"), labels(javaChildren));
		for (final Object child : javaChildren) {
			assertEquals(java, ((FeaturePackage) child).getParent());
		}

		final FeaturePackageRoot resources = new FeaturePackageRoot(feature.getFolder("src/main/resources"), feature);
		assertEquals(List.of(feature.getFolder("src/main/resources/config")), FeaturePackageStructure.getSourceFolderChildren(resources));
	}

	@Test
	public void onlyExistingMavenSourceFoldersAreShown() throws CoreException {
		createFile(feature, "src/main/resources/app.properties");

		assertEquals(Set.of("src/main/resources"), labels(FeaturePackageStructure.getFeatureFolderChildren(feature)));
	}

	@Test
	public void otherFoldersInSrcRemainVisible() throws CoreException {
		createFile(feature, "src/main/java/de/A.java");
		createFile(feature, "src/it/java/de/AIT.java");

		final List<Object> children = FeaturePackageStructure.getFeatureFolderChildren(feature);
		assertEquals(Set.of("src/main/java", "src"), labels(children));

		// in the folder src, the folder main is hidden, because it is shown as src/main/java
		final Collection<Object> srcChildren = new ArrayList<>(List.of(feature.getFolder("src/main"), feature.getFolder("src/it")));
		FeaturePackageStructure.removeResourcesInSourceFolders(feature, srcChildren);
		assertEquals(Set.of("it"), labels(srcChildren));
	}

	@Test
	public void otherFoldersInMainRemainVisible() throws CoreException {
		// target folder src: the feature folders contain main/java etc.
		createFile(feature, "main/java/de/A.java");
		createFile(feature, "main/webapp/index.html");

		assertEquals(Set.of("main/java", "main"), labels(FeaturePackageStructure.getFeatureFolderChildren(feature)));

		final Collection<Object> mainChildren = new ArrayList<>(List.of(feature.getFolder("main/java"), feature.getFolder("main/webapp")));
		FeaturePackageStructure.removeResourcesInSourceFolders(feature, mainChildren);
		assertEquals(Set.of("webapp"), labels(mainChildren));
	}

	@Test
	public void mavenTestSourceFoldersAreShownAsOneNode() throws CoreException {
		createFile(feature, "src/main/java/de/A.java");
		createFile(feature, "src/main/resources/app.properties");
		createFile(feature, "src/test/java/de/ATest.java");
		createFile(feature, "src/test/resources/test.properties");

		// src, src/main and src/test are not shown, neither as folders nor as packages
		assertEquals(Set.of("src/main/java", "src/main/resources", "src/test/java", "src/test/resources"),
				labels(FeaturePackageStructure.getFeatureFolderChildren(feature)));

		final FeaturePackageRoot testJava = new FeaturePackageRoot(feature.getFolder("src/test/java"), feature);
		assertEquals(Set.of("de"), labels(FeaturePackageStructure.getPackageRootChildren(testJava, testJava.getFolder())));
	}

	@Test
	public void sourceFoldersForTargetFolderSrc() throws CoreException {
		// target folder src: the feature folders contain main/java, main/resources, test/java and test/resources
		createFile(feature, "main/java/de/ovgu/a/A.java");
		createFile(feature, "main/resources/META-INF/MANIFEST.MF");
		final IFile test = createFile(feature, "test/java/de/ovgu/a/ATest.java");
		createFile(feature, "test/resources/test.properties");
		createFile(feature, "pom.xml");

		final List<Object> children = FeaturePackageStructure.getFeatureFolderChildren(feature);
		// main and test are not shown, neither as folders nor as packages
		assertEquals(Set.of("main/java", "main/resources", "test/java", "test/resources", "pom.xml"), labels(children));

		final FeaturePackageRoot mainJava = new FeaturePackageRoot(feature.getFolder("main/java"), feature);
		final List<Object> mainChildren = FeaturePackageStructure.getSourceFolderChildren(mainJava);
		assertEquals(Set.of("de.ovgu.a"), labels(mainChildren));
		assertEquals(mainJava, ((FeaturePackage) mainChildren.get(0)).getParent());

		final FeaturePackageRoot mainResources = new FeaturePackageRoot(feature.getFolder("main/resources"), feature);
		assertEquals(List.of(feature.getFolder("main/resources/META-INF")), FeaturePackageStructure.getSourceFolderChildren(mainResources));

		// resources in the source folders are shown in their packages
		final FeaturePackageRoot testJava = new FeaturePackageRoot(feature.getFolder("test/java"), feature);
		final Object parent = FeaturePackageStructure.getParent(test, feature);
		assertEquals(new FeaturePackage(null, testJava.getFolder(), feature.getFolder("test/java/de/ovgu/a")), parent);
		assertEquals(testJava, ((FeaturePackage) parent).getParent());
		assertEquals(feature, FeaturePackageStructure.getParent(feature.getFolder("test/java"), feature));
		assertEquals(testJava, FeaturePackageStructure.getSourceFolder(test, feature));
	}

	@Test
	public void sourceFoldersForTargetFolderSrcMain() throws CoreException {
		// target folder src/main: the feature folders contain java and resources
		createFile(feature, "java/de/ovgu/a/A.java");
		createFile(feature, "java/Main.java");
		createFile(feature, "resources/app.properties");

		assertEquals(Set.of("java", "resources"), labels(FeaturePackageStructure.getFeatureFolderChildren(feature)));

		final FeaturePackageRoot java = new FeaturePackageRoot(feature.getFolder("java"), feature);
		assertEquals(Set.of("(default package)", "de.ovgu.a"), labels(FeaturePackageStructure.getPackageRootChildren(java, java.getFolder())));
		assertEquals("java", java.getLabel());
	}

	@Test
	public void javaSourceFolderForNewElements() throws CoreException {
		// without Maven layout: the feature folder
		assertEquals(feature, FeaturePackageStructure.getJavaSourceFolder(feature));

		createFile(feature, "test/java/de/ATest.java");
		createFile(feature, "main/resources/app.properties");
		// main/java does not exist yet, but is on the level of the existing source folders
		assertEquals(feature.getFolder("main/java"), FeaturePackageStructure.getJavaSourceFolder(feature));

		createFile(feature, "main/java/de/A.java");
		assertEquals(feature.getFolder("main/java"), FeaturePackageStructure.getJavaSourceFolder(feature));
	}

	@Test
	public void javaSourceFolderForNewElementsOnOtherLevels() throws CoreException {
		createFile(feature, "src/test/java/de/ATest.java");
		assertEquals(feature.getFolder("src/main/java"), FeaturePackageStructure.getJavaSourceFolder(feature));

		final IFolder other = project.getFolder("features/Other");
		createFile(other, "resources/app.properties");
		assertEquals(other.getFolder("java"), FeaturePackageStructure.getJavaSourceFolder(other));
	}

	@Test
	public void javaAndTestSourceFolders() throws CoreException {
		createFile(feature, "test/java/de/ATest.java");
		createFile(feature, "test/resources/test.properties");

		assertTrue(FeaturePackageStructure.isJavaSourceFolder(new FeaturePackageRoot(feature.getFolder("test/java"), feature)));
		assertTrue(!FeaturePackageStructure.isJavaSourceFolder(new FeaturePackageRoot(feature.getFolder("test/resources"), feature)));
		assertNull(FeaturePackageStructure.getSourceFolder(feature.getFolder("test"), feature));
	}

	@Test
	public void parentsOfResources() throws CoreException {
		final IFile main = createFile(feature, "Main.java");
		final IFile readme = createFile(feature, "readme.txt");
		final IFile a = createFile(feature, "de/ovgu/a/A.java");

		assertEquals(new FeaturePackage(feature, feature, feature), FeaturePackageStructure.getParent(main, feature));
		assertEquals(feature, FeaturePackageStructure.getParent(readme, feature));
		assertEquals(new FeaturePackage(feature, feature, feature.getFolder("de/ovgu/a")), FeaturePackageStructure.getParent(a, feature));
	}

	@Test
	public void parentsOfResourcesInMavenSourceFolders() throws CoreException {
		final IFile a = createFile(feature, "src/main/java/de/ovgu/a/A.java");
		final IFile pom = createFile(feature, "pom.xml");
		final IFolder java = feature.getFolder("src/main/java");

		final Object parent = FeaturePackageStructure.getParent(a, feature);
		assertEquals(new FeaturePackage(null, java, java.getFolder("de/ovgu/a")), parent);
		assertEquals(new FeaturePackageRoot(java, feature), ((FeaturePackage) parent).getParent());
		assertEquals(feature, FeaturePackageStructure.getParent(java, feature));
		// resources outside of the source folders keep their usual parent
		assertNull(FeaturePackageStructure.getParent(pom, feature));
	}

	@Test
	public void packageNamesAndAdapters() {
		final FeaturePackage featurePackage = new FeaturePackage(feature, feature, feature.getFolder("de/ovgu/a"));
		assertEquals("de.ovgu.a", featurePackage.getName());
		assertEquals(feature.getFolder("de/ovgu/a"), featurePackage.getAdapter(IResource.class));

		final FeaturePackage defaultPackage = new FeaturePackage(feature, feature, feature);
		assertTrue(defaultPackage.isDefaultPackage());
		assertEquals(FeaturePackage.DEFAULT_PACKAGE_NAME, defaultPackage.getName());
		// deleting the default package must not delete the feature folder
		assertNull(defaultPackage.getAdapter(IResource.class));

		assertEquals("src/main/java", new FeaturePackageRoot(feature.getFolder("src/main/java"), feature).getLabel());
	}

	private static Set<String> labels(Collection<?> elements) {
		final Set<String> labels = new TreeSet<>();
		final Set<Object> unique = new HashSet<>(elements);
		assertEquals("duplicate elements: " + elements, elements.size(), unique.size());
		for (final Object element : elements) {
			if (element instanceof FeaturePackage) {
				labels.add(((FeaturePackage) element).getName());
			} else if (element instanceof FeaturePackageRoot) {
				labels.add(((FeaturePackageRoot) element).getLabel());
			} else {
				labels.add(((IResource) element).getName());
			}
		}
		return labels;
	}

	private static IFile createFile(IFolder parent, String path) throws CoreException {
		final IFile file = parent.getFile(new Path(path));
		createFolder(file.getParent());
		file.create(new ByteArrayInputStream(new byte[0]), true, null);
		return file;
	}

	private static void createFolder(IFolder parent, String path) throws CoreException {
		createFolder(parent.getFolder(new Path(path)));
	}

	private static void createFolder(IContainer container) throws CoreException {
		if ((container instanceof IFolder) && !container.exists()) {
			createFolder(container.getParent());
			((IFolder) container).create(true, true, null);
		}
	}
}
