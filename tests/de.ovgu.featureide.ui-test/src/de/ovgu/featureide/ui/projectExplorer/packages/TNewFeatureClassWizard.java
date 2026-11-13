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
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.ui.projectExplorer.packages.NewFeatureClassWizard.Kind;

/**
 * Tests the creation of packages and classes in feature folders by {@link NewFeaturePackageWizard} and {@link NewFeatureClassWizard}.
 *
 * @author Philipp Hehnle
 */
public class TNewFeatureClassWizard {

	private IProject project;
	private IFolder feature;

	@Before
	public void createProject() throws CoreException {
		project = ResourcesPlugin.getWorkspace().getRoot().getProject("TNewFeatureClassWizard");
		if (project.exists()) {
			project.delete(true, true, null);
		}
		project.create(null);
		project.open(null);
		feature = project.getFolder("features");
		feature.create(true, true, null);
		feature = feature.getFolder("Base");
		feature.create(true, true, null);
	}

	@After
	public void deleteProject() throws CoreException {
		project.delete(true, true, null);
	}

	@Test
	public void sourceOfClass() {
		assertEquals("package de.hehnle.test;\n\npublic class Test {\n\n}\n", NewFeatureClassWizard.createSource("de.hehnle.test", "Test", Kind.CLASS, false, "\n"));
	}

	@Test
	public void sourceOfClassWithMain() {
		assertEquals("package de.hehnle.test;\n\npublic class Test {\n\n\tpublic static void main(String[] args) {\n\n\t}\n\n}\n",
				NewFeatureClassWizard.createSource("de.hehnle.test", "Test", Kind.CLASS, true, "\n"));
	}

	@Test
	public void sourceOfOtherKindsInDefaultPackage() {
		assertEquals("public interface I {\r\n\r\n}\r\n", NewFeatureClassWizard.createSource("", "I", Kind.INTERFACE, false, "\r\n"));
		assertEquals("public enum E {\n\n}\n", NewFeatureClassWizard.createSource("", "E", Kind.ENUM, false, "\n"));
		// the main method is only created for classes
		assertEquals("public record R() {\n\n}\n", NewFeatureClassWizard.createSource("", "R", Kind.RECORD, true, "\n"));
	}

	@Test
	public void createPackageCreatesNestedFolders() throws CoreException {
		final FeatureJavaLocation location = new FeatureJavaLocation(feature, feature, "");
		location.createPackage("de.hehnle.test");

		assertTrue(feature.getFolder("de/hehnle/test").exists());
		assertEquals(new FeaturePackage(feature, feature, feature.getFolder("de/hehnle/test")), location.getPackageNode("de.hehnle.test"));
		assertEquals("de.hehnle.test", location.getPackageNode("de.hehnle.test").getName());
	}

	@Test
	public void createPackageInMavenSourceFolder() throws CoreException {
		final IFolder java = feature.getFolder("src/main/java");
		final FeatureJavaLocation location = new FeatureJavaLocation(feature, java, "");
		location.createPackage("de.a");

		assertTrue(feature.getFolder("src/main/java/de/a").exists());
		assertEquals(new FeaturePackageRoot(java, feature), location.getPackageNode("de.a").getParent());
	}

	@Test
	public void createTypeCreatesPackageAndFile() throws CoreException, IOException {
		final FeatureJavaLocation location = new FeatureJavaLocation(feature, feature, "");
		final IFile file = NewFeatureClassWizard.createType(location, "de.hehnle.test", "Test", Kind.CLASS, false);

		assertEquals(feature.getFile("de/hehnle/test/Test.java"), file);
		final String content = read(file);
		assertTrue(content, content.startsWith("package de.hehnle.test;"));
		assertTrue(content, content.contains("public class Test {"));

		try {
			NewFeatureClassWizard.createType(location, "de.hehnle.test", "Test", Kind.CLASS, false);
			fail("existing type overwritten");
		} catch (final CoreException e) {
			// expected
		}
	}

	@Test
	public void validatesPackageNames() {
		assertEquals(IStatus.OK, FeatureJavaLocation.validatePackageName("de.hehnle.test", false).getSeverity());
		assertEquals(IStatus.ERROR, FeatureJavaLocation.validatePackageName("de.hehnle.", false).getSeverity());
		assertEquals(IStatus.ERROR, FeatureJavaLocation.validatePackageName("de.my-package", false).getSeverity());
		assertEquals(IStatus.WARNING, FeatureJavaLocation.validatePackageName("De.Hehnle", false).getSeverity());
		assertEquals(IStatus.ERROR, FeatureJavaLocation.validatePackageName("", false).getSeverity());
		assertEquals(IStatus.OK, FeatureJavaLocation.validatePackageName("", true).getSeverity());
	}

	@Test
	public void validatesTypeNames() {
		assertEquals(IStatus.OK, FeatureJavaLocation.validateTypeName("Test").getSeverity());
		assertEquals(IStatus.WARNING, FeatureJavaLocation.validateTypeName("test").getSeverity());
		assertEquals(IStatus.ERROR, FeatureJavaLocation.validateTypeName("1Test").getSeverity());
		assertEquals(IStatus.ERROR, FeatureJavaLocation.validateTypeName("de.Test").getSeverity());
		assertEquals(IStatus.ERROR, FeatureJavaLocation.validateTypeName("").getSeverity());
	}

	private static String read(IFile file) throws CoreException, IOException {
		try (InputStream in = file.getContents()) {
			return new String(in.readAllBytes(), file.getCharset());
		}
	}
}
