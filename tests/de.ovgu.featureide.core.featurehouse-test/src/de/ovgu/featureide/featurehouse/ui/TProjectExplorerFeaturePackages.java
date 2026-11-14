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
package de.ovgu.featureide.featurehouse.ui;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.internal.navigator.wizards.CommonWizardDescriptorManager;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.navigator.CommonViewer;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.ui.projectExplorer.packages.FeatureJavaLocation;
import de.ovgu.featureide.ui.projectExplorer.packages.FeaturePackage;
import de.ovgu.featureide.ui.projectExplorer.packages.FeaturePackageRoot;
import de.ovgu.featureide.ui.projectExplorer.packages.NewFeatureClassWizard;
import de.ovgu.featureide.ui.projectExplorer.packages.NewFeaturePackageWizard;

/**
 * Tests that the Project Explorer shows the content of FeatureHouse feature folders as packages.
 *
 * @author Philipp Hehnle
 */
public class TProjectExplorerFeaturePackages {

	private static final String FEATUREHOUSE = "de.ovgu.featureide.composer.featurehouse";

	private IProject project;
	private CommonViewer viewer;

	@Before
	public void createFeatureHouseProject() throws Exception {
		project = ResourcesPlugin.getWorkspace().getRoot().getProject("TProjectExplorerFeaturePackages");
		if (project.exists()) {
			project.delete(true, true, null);
		}
		project.create(null);
		project.open(null);

		final IProjectDescription description = project.getDescription();
		description.setNatureIds(new String[] { JavaCore.NATURE_ID });
		project.setDescription(description, null);
		final IFolder build = project.getFolder("src");
		build.create(true, true, null);
		JavaCore.create(project).setRawClasspath(new IClasspathEntry[] { JavaCore.newSourceEntry(build.getFullPath()) }, project.getFullPath().append("bin"),
				null);

		CorePlugin.setupFeatureProject(project, FEATUREHOUSE, "features", "configs", "src", false, true, true, false);
		for (int i = 0; (i < 100) && (CorePlugin.getFeatureProject(project) == null); i++) {
			processUIEvents();
			Thread.sleep(50);
		}
		assertNotNull("not a feature project", CorePlugin.getFeatureProject(project));

		final CommonNavigator projectExplorer =
			(CommonNavigator) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().showView(IPageLayout.ID_PROJECT_EXPLORER);
		viewer = projectExplorer.getCommonViewer();
	}

	@After
	public void deleteProject() throws CoreException {
		project.delete(true, true, null);
	}

	@Test
	public void featureFolderShowsPackages() throws CoreException {
		final IFolder feature = project.getFolder("features/Hello");
		createFile(feature, "Main.java");
		final IFile a = createFile(feature, "de/ovgu/a/A.java");

		assertEquals(Set.of("(default package)", "de.ovgu.a"), labels(children(feature)));

		final FeaturePackage featurePackage = new FeaturePackage(feature, feature, feature.getFolder("de/ovgu/a"));
		assertEquals(Set.of("A.java"), labels(children(featurePackage)));
		// needed to reveal files, e.g. with "Link with Editor"
		assertEquals(featurePackage, contentProvider().getParent(a));

		assertNotNull(labelProvider().getImage(featurePackage));
	}

	@Test
	public void mavenSourceFoldersAreShownAsOneNode() throws CoreException {
		final IFolder feature = project.getFolder("features/Maven");
		createFile(feature, "src/main/java/de/b/B.java");
		createFile(feature, "pom.xml");

		assertEquals(Set.of("src/main/java", "pom.xml"), labels(children(feature)));
		final FeaturePackageRoot root = new FeaturePackageRoot(feature.getFolder("src/main/java"), feature);
		assertEquals(Set.of("de.b"), labels(children(root)));
	}

	@Test
	public void mavenSourceFoldersForTargetFolderSrc() throws CoreException {
		// the target folder of this project is src, so the feature folders contain main/java, test/java etc.
		final IFolder feature = project.getFolder("features/MavenSrc");
		createFile(feature, "main/java/de/b/B.java");
		createFile(feature, "main/resources/app.properties");
		final IFile test = createFile(feature, "test/java/de/b/BTest.java");
		createFile(feature, "test/resources/test.properties");

		assertEquals(Set.of("main/java", "main/resources", "test/java", "test/resources"), labels(children(feature)));
		final FeaturePackageRoot testRoot = new FeaturePackageRoot(feature.getFolder("test/java"), feature);
		assertEquals(Set.of("de.b"), labels(children(testRoot)));
		assertEquals(new FeaturePackage(testRoot, testRoot.getFolder(), feature.getFolder("test/java/de/b")), contentProvider().getParent(test));

		// resource folders show normal folders, no packages
		createFile(feature, "main/resources/de/b/b.properties");
		final FeaturePackageRoot resourcesRoot = new FeaturePackageRoot(feature.getFolder("main/resources"), feature);
		assertEquals(Set.of("app.properties", "de"), labels(children(resourcesRoot)));
		assertEquals(Set.of("b"), labels(children(feature.getFolder("main/resources/de"))));
	}

	@Test
	public void newPackageAndClassAreInTheNewMenuOfFeatureContent() throws CoreException {
		final IFolder feature = project.getFolder("features/Hello");
		final IFile a = createFile(feature, "de/ovgu/a/A.java");
		final FeaturePackage featurePackage = new FeaturePackage(feature, feature, feature.getFolder("de/ovgu/a"));
		final Set<String> wizards = Set.of(NewFeaturePackageWizard.ID, NewFeatureClassWizard.ID);

		for (final Object element : new Object[] { feature, featurePackage, a }) {
			assertTrue("missing for " + element, newMenuEntries(element).containsAll(wizards));
		}
		// not outside of feature folders
		final IFile readme = project.getFile("readme.txt");
		readme.create(new ByteArrayInputStream(new byte[0]), true, null);
		for (final Object element : new Object[] { project, project.getFolder("features"), readme }) {
			assertTrue("shown for " + element, Collections.disjoint(newMenuEntries(element), wizards));
		}
	}

	@Test
	public void locationsFromSelection() throws CoreException {
		final IFolder feature = project.getFolder("features/Hello");
		final IFile a = createFile(feature, "de/ovgu/a/A.java");

		assertLocation(feature, "", FeatureJavaLocation.of(feature));
		assertLocation(feature, "de.ovgu.a", FeatureJavaLocation.of(new FeaturePackage(feature, feature, feature.getFolder("de/ovgu/a"))));
		assertLocation(feature, "de.ovgu.a", FeatureJavaLocation.of(a));

		final IFolder maven = project.getFolder("features/Maven");
		createFile(maven, "src/main/java/de/b/B.java");
		createFile(maven, "pom.xml");
		assertLocation(maven.getFolder("src/main/java"), "", FeatureJavaLocation.of(maven));
		assertLocation(maven.getFolder("src/main/java"), "", FeatureJavaLocation.of(maven.getFile("pom.xml")));
		assertLocation(maven.getFolder("src/main/java"), "de.b", FeatureJavaLocation.of(maven.getFile("src/main/java/de/b/B.java")));

		// main/java and test/java, e.g. for the target folder src
		final IFolder mavenSrc = project.getFolder("features/MavenSrc");
		createFile(mavenSrc, "main/java/de/b/B.java");
		createFile(mavenSrc, "main/resources/app.properties");
		createFile(mavenSrc, "test/java/de/b/BTest.java");
		assertLocation(mavenSrc.getFolder("main/java"), "", FeatureJavaLocation.of(mavenSrc));
		assertLocation(mavenSrc.getFolder("main/java"), "", FeatureJavaLocation.of(mavenSrc.getFile("main/resources/app.properties")));
		// new classes next to a test are created in the test source folder
		assertLocation(mavenSrc.getFolder("test/java"), "de.b", FeatureJavaLocation.of(mavenSrc.getFile("test/java/de/b/BTest.java")));
		assertLocation(mavenSrc.getFolder("test/java"), "",
				FeatureJavaLocation.of(new FeaturePackageRoot(mavenSrc.getFolder("test/java"), mavenSrc)));
		// not in resource folders
		assertLocation(mavenSrc.getFolder("main/java"), "",
				FeatureJavaLocation.of(new FeaturePackageRoot(mavenSrc.getFolder("main/resources"), mavenSrc)));

		// not in a feature folder
		assertNull(FeatureJavaLocation.of(project.getFolder("features")));
	}

	@Test
	public void newPackageWizardCreatesNestedFolders() throws CoreException {
		final IFolder feature = project.getFolder("features/Hello");
		createFile(feature, "Main.java");

		final NewFeaturePackageWizard wizard = new NewFeaturePackageWizard();
		runWizard(wizard, feature, texts -> {
			assertEquals("Hello: source folder", project.getName() + "/features/Hello", texts.get(0).getText());
			texts.get(1).setText("de.hehnle.test");
		});

		assertTrue(feature.getFolder("de/hehnle/test").exists());
		processUIEvents();
		assertNotNull("new package not revealed", viewer.testFindItem(new FeaturePackage(feature, feature, feature.getFolder("de/hehnle/test"))));
	}

	@Test
	public void newClassWizardCreatesClassInSelectedPackage() throws CoreException, IOException {
		final IFolder feature = project.getFolder("features/Hello");
		createFile(feature, "de/hehnle/test/Other.java");
		final FeaturePackage featurePackage = new FeaturePackage(feature, feature, feature.getFolder("de/hehnle/test"));

		final NewFeatureClassWizard wizard = new NewFeatureClassWizard();
		runWizard(wizard, featurePackage, texts -> {
			assertEquals("package from selection", "de.hehnle.test", texts.get(1).getText());
			texts.get(2).setText("Test");
		});

		final IFile file = feature.getFile("de/hehnle/test/Test.java");
		assertTrue(file.exists());
		try (InputStream in = file.getContents()) {
			final String content = new String(in.readAllBytes(), file.getCharset());
			assertTrue(content, content.startsWith("package de.hehnle.test;"));
			assertTrue(content, content.contains("public class Test {"));
		}
		PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().closeAllEditors(false);
	}

	@Test
	public void wizardsAreRegistered() {
		assertNotNull(PlatformUI.getWorkbench().getNewWizardRegistry().findWizard(NewFeaturePackageWizard.ID));
		assertNotNull(PlatformUI.getWorkbench().getNewWizardRegistry().findWizard(NewFeatureClassWizard.ID));
	}

	private Set<String> newMenuEntries(Object element) {
		return Set.of(CommonWizardDescriptorManager.getInstance().getEnabledCommonWizardDescriptorIds(element, CommonWizardDescriptorManager.WIZARD_TYPE_NEW,
				viewer.getNavigatorContentService()));
	}

	private static void assertLocation(IContainer root, String packageName, FeatureJavaLocation location) {
		assertNotNull(location);
		assertEquals(root, location.getRoot());
		assertEquals(packageName, location.getPackageName());
	}

	/**
	 * Opens the wizard for the selected element, lets the test fill the text fields of its page (in their order on the page), and finishes it.
	 */
	private static void runWizard(INewWizard wizard, Object selected, Consumer<List<Text>> fillIn) {
		wizard.init(PlatformUI.getWorkbench(), new StructuredSelection(selected));
		final WizardDialog dialog = new WizardDialog(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell(), wizard);
		dialog.create();
		try {
			final List<Text> texts = new ArrayList<>();
			collectTexts(wizard.getPages()[0].getControl(), texts);
			fillIn.accept(texts);
			assertTrue("wizard cannot finish: " + wizard.getPages()[0].getErrorMessage(), wizard.canFinish());
			assertTrue(wizard.performFinish());
		} finally {
			dialog.close();
		}
	}

	private static void collectTexts(Control control, List<Text> texts) {
		if (control instanceof Text) {
			texts.add((Text) control);
		} else if (control instanceof Composite) {
			for (final Control child : ((Composite) control).getChildren()) {
				collectTexts(child, texts);
			}
		}
	}

	@Test
	public void filesOutsideOfFeatureFoldersKeepTheirParents() throws CoreException {
		final IFile readme = project.getFile("readme.txt");
		readme.create(new ByteArrayInputStream(new byte[0]), true, null);
		final IFile other = createFile(project.getFolder("other"), "x.txt");
		final IFile composed = createFile(project.getFolder("src"), "p/Q.java");

		assertEquals(project, contentProvider().getParent(readme));
		assertEquals(project.getFolder("other"), contentProvider().getParent(other));
		// files in Java source folders are still handled by the Java content
		assertEquals(JavaCore.create(project.getFolder("src/p")), contentProvider().getParent(composed));
	}

	@Test
	public void newFilesAppearInTheTree() throws Exception {
		final IFolder feature = project.getFolder("features/Hello");
		createFile(feature, "de/ovgu/a/A.java");
		processUIEvents();
		viewer.expandToLevel(feature, 1);
		processUIEvents();
		assertNotNull("package not shown in the tree", viewer.testFindItem(new FeaturePackage(feature, feature, feature.getFolder("de/ovgu/a"))));

		// the new package is only shown if the feature folder is refreshed after the resource change
		createFile(feature, "de/ovgu/c/C.java");
		processUIEvents();
		assertNotNull("new package not shown in the tree", viewer.testFindItem(new FeaturePackage(feature, feature, feature.getFolder("de/ovgu/c"))));
	}

	private Object[] children(Object parent) {
		return contentProvider().getChildren(parent);
	}

	private ITreeContentProvider contentProvider() {
		return (ITreeContentProvider) viewer.getContentProvider();
	}

	private ILabelProvider labelProvider() {
		return (ILabelProvider) viewer.getLabelProvider();
	}

	private Set<String> labels(Object[] elements) {
		final Set<String> labels = new TreeSet<>();
		for (final Object element : elements) {
			labels.add(labelProvider().getText(element).trim());
		}
		return labels;
	}

	private static void processUIEvents() {
		final Display display = Display.getCurrent();
		if (display != null) {
			while (display.readAndDispatch()) {}
		}
	}

	private static IFile createFile(IFolder parent, String path) throws CoreException {
		final IFile file = parent.getFile(new Path(path));
		createFolder(file.getParent());
		file.create(new ByteArrayInputStream(new byte[0]), true, null);
		return file;
	}

	private static void createFolder(IContainer container) throws CoreException {
		if ((container instanceof IFolder) && !container.exists()) {
			createFolder(container.getParent());
			((IFolder) container).create(true, true, null);
		}
	}
}
