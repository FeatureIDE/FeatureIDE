/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl.io.writer;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.launching.IVMInstall;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jdt.launching.LibraryLocation;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.reader.FeatureListReader;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.mpl.signature.filter.ViewTagFilter;

/**
 * Creates a new java project with only interfaces for one configuration.
 * 
 * @author Sebastian Krieter
 */
public class JavaProjectWriter extends AbstractWriter {

	public JavaProjectWriter(InterfaceProject interfaceProject) {
		super(interfaceProject);
	}
	
	public void buildJavaProject(IFile featureListFile, String name) {		
		if (interfaceProject != null) {
			//TODO MPL: save as ids
			int[] featureList = interfaceProject.getFeatureIDs((new FeatureListReader(featureListFile)).read());
			if (featureList != null) {
				final ProjectSignatures projectSignatures = interfaceProject.getProjectSignatures();
				
				SignatureIterator it = projectSignatures.createIterator();
				it.addFilter(new FeatureFilter(featureList));
				it.addFilter(new ViewTagFilter(interfaceProject.getFilterViewTag()));
				ProjectStructure javaSig = new ProjectStructure(it);
				
				IJavaProject javaProject = createJavaProject(interfaceProject.getProjectReference().getName() + "_java_" + name.substring(name.lastIndexOf('_') + 1));
				if (javaProject != null) {					
					for (AbstractClassFragment cls : javaSig.getClasses()) {
						IFolder sourceFolder = javaProject.getProject().getFolder(Path.fromPortableString("src"));
						try {
							IPackageFragment featurePackage = javaProject.getPackageFragmentRoot(sourceFolder).createPackageFragment(cls.getSignature().getPackage(), true, null);
							featurePackage.createCompilationUnit(cls.getSignature().getName() + ".java", cls.toString(), true, null);
						} catch (JavaModelException e) {
							MPLPlugin.getDefault().logError(e);
						} 
					}
					MPLPlugin.getDefault().logInfo("Created Java Project");
				}
			}
		}		
	}
	
	private IJavaProject createJavaProject(String projectName) {
		IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
		
		IProjectDescription description = ResourcesPlugin.getWorkspace().newProjectDescription(projectName);
		description.setNatureIds(new String[]{JavaCore.NATURE_ID});
		ICommand build = description.newCommand();
		build.setBuilderName(JavaCore.BUILDER_ID);
		description.setBuildSpec(new ICommand[] { build });
		
		try {
			project.delete(true, true, null);
			project.create(description, null);
			project.open(null);

			IJavaProject javaProject = JavaCore.create(project);
			javaProject.open(null);

			List<IClasspathEntry> entries = new LinkedList<IClasspathEntry>();

			IPath sourcePath = Path.fromPortableString("src");
			IFolder sourceFolder = project.getFolder(sourcePath);
			sourceFolder.create(true, true, null);
			sourcePath = project.getFolder(sourcePath).getFullPath();

			IPath binPath = Path.fromPortableString("bin");
			project.getFolder(binPath).create(false, true, null);
			binPath = project.getFolder(binPath).getFullPath();

			entries.add(JavaCore.newSourceEntry(sourcePath, new IPath[0], binPath));

			IVMInstall vmInstall = JavaRuntime.getDefaultVMInstall();
			for (LibraryLocation location : JavaRuntime.getLibraryLocations(vmInstall)) {
				entries.add(JavaCore.newLibraryEntry(location.getSystemLibraryPath(), null, null));
			}

			javaProject.setRawClasspath(entries.toArray(new IClasspathEntry[entries.size()]), null);
			
			return javaProject;
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
		}
		return null;
	}
}
