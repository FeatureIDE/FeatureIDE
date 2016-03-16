/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.framework;

import java.io.File;
import java.nio.file.FileSystems;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.launching.IVMInstall;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jdt.launching.LibraryLocation;
import org.w3c.dom.Comment;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.ovgu.featureide.core.framework.activator.FrameworkCorePlugin;

/**
 * Class for creating the sub-projects
 * 
 * @author Daniel Hohmann
 */
public class FrameworkProjectCreator {

	private static String[] INTERFACETAG_STRUCTURE = { "\t<interface id=\"fullInterfaceName\">", "\t\t<class>fullClassName</class>", "\t</interface>" };

	/**
	 * Creates a new subproject inside a folder
	 * 
	 * @param name - project name
	 * @param destination - folder which contains the subproject
	 * @throws CoreException
	 */
	public static void createSubprojectFolder(String name, IFolder destination) throws CoreException {
		IProjectDescription description = ResourcesPlugin.getWorkspace().newProjectDescription(name);
		description.setLocation(destination.getLocation());
		
		IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(name);
		if (project.exists()) {
			return;
		}
		project.create(description, null);
		project.open(null);
		
		description.setNatureIds(new String[] { JavaCore.NATURE_ID });
		project.setDescription(description, null);

		IJavaProject javaProject = JavaCore.create(project);
		javaProject.open(null);

		IFolder binFolder = project.getFolder("bin");
		binFolder.create(true, true, null);
		javaProject.setOutputLocation(binFolder.getFullPath(), null);

		List<IClasspathEntry> entries = new ArrayList<IClasspathEntry>();
		IVMInstall vmInstall = JavaRuntime.getDefaultVMInstall();
		LibraryLocation[] locations = JavaRuntime.getLibraryLocations(vmInstall);
		for (LibraryLocation element : locations) {
			entries.add(JavaCore.newLibraryEntry(element.getSystemLibraryPath(), null, null));
		}
		javaProject.setRawClasspath(entries.toArray(new IClasspathEntry[entries.size()]), null);

		IFolder sourceFolder = project.getFolder("src");
		sourceFolder.create(false, true, null);

		IPackageFragmentRoot srcRoot = javaProject.getPackageFragmentRoot(sourceFolder);
		IClasspathEntry[] oldEntries = javaProject.getRawClasspath();
		IClasspathEntry[] newEntries = new IClasspathEntry[oldEntries.length + 1];
		System.arraycopy(oldEntries, 0, newEntries, 0, oldEntries.length);
		newEntries[oldEntries.length] = JavaCore.newSourceEntry(srcRoot.getPath());
		javaProject.setRawClasspath(newEntries, null);

		IFile infoXML = destination.getFile("info.xml");
		if (!infoXML.exists()) {
			createInfoXML(destination);
		}
	}
	/**
	 * Creates an <code>info.xml</code> file for subproject
	 * 
	 * @param destination
	 */
	private static void createInfoXML(IFolder destination) {
		try {
			/** Create builder **/
			DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
			DocumentBuilder dBuilder;
			dBuilder = dbFactory.newDocumentBuilder();
			Document infoXML = dBuilder.newDocument();

			/** Create content **/
			Element plugins = infoXML.createElement("plugins");
			infoXML.appendChild(plugins);

			for (String comm : INTERFACETAG_STRUCTURE) {
				Comment interfaceTag = infoXML.createComment(comm);
				plugins.appendChild(interfaceTag);
			}

			infoXML.normalizeDocument();

			/** Create output **/
			TransformerFactory transformerFactory = TransformerFactory.newInstance();
			Transformer transformer = transformerFactory.newTransformer();
			transformer.setOutputProperty(OutputKeys.INDENT, "yes");
			DOMSource source = new DOMSource(infoXML);
			StreamResult result = new StreamResult(
					new File(destination.getLocationURI()).getAbsolutePath().concat(FileSystems.getDefault().getSeparator() + "info.xml"));
			transformer.transform(source, result);
		} catch (ParserConfigurationException | TransformerException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}
}
