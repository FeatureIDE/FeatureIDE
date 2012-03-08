/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ahead.actions;

import java.util.AbstractList;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IClasspathAttribute;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.ClasspathEntry;
import org.eclipse.jdt.internal.core.JavaProject;

import de.ovgu.featureide.ahead.AheadComposer;
import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;

/**
 * Changes the composer of an feature project project to <code>AHEAD</code>.
 * 
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class FeatureHouseToAHEADConversion extends ComposerConversion {
	private FSTModel model;

	/**
	 * Changes the composer of the given feature project to <code>AHEAD</code>.
	 * @param featureProject
	 */
	public FeatureHouseToAHEADConversion(final IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		this.featureProject = featureProject; 
		AheadCorePlugin.getDefault().logInfo("Change the composer of project " 
				+ featureProject.getProjectName() + 
				" from FeatureHouse to AHEAD.");
		Job job = new Job("Change composer.") {
			protected IStatus run(IProgressMonitor monitor) {
				try {
					setJavaBuildPath(featureProject);
					monitor.beginTask("Change composer.", 2);
					monitor.subTask("Build full FSTModel.");
					buildFullFSTModel();
					model = featureProject.getFSTModel();
					monitor.worked(1);
					monitor.subTask("Replace keywords.");
					start(featureProject);
					monitor.worked(1);
				} finally {
					monitor.done();
				}
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.BUILD);
		job.schedule();
		
	}

	/**
	 * 
	 */
	protected void buildFullFSTModel() {
		featureProject.getComposer().buildFSTModel();
	}

	/**
	 * Sets the java build path to the build folder of the given feature project.
	 * @param featureProject
	 */
	private void setJavaBuildPath(IFeatureProject featureProject) {
		try {	
			JavaProject javaProject = new JavaProject(featureProject.getProject(), null);
			IClasspathEntry[] classpathEntries = javaProject.getRawClasspath();
			for (int i = 0; i < classpathEntries.length; i++) {
				/** change the actual source entry **/
				if (classpathEntries[i].getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					classpathEntries[i] = setSourceEntry(classpathEntries[i]);
					javaProject.setRawClasspath(classpathEntries, null);
					return;
				}
			}
			
			/** case: no source entry **/
			IClasspathEntry[] newEntries = new IClasspathEntry[classpathEntries.length + 1];
			System.arraycopy(classpathEntries, 0, newEntries, 0, classpathEntries.length);
			newEntries[newEntries.length - 1] = getSourceEntry();
			javaProject.setRawClasspath(classpathEntries, null);
		} catch (JavaModelException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * Set the source path of given <code>ClasspathEntry</code> to the current build path
	 * @param e The entry to set
	 * @return The entry with the new source path
	 */
	public IClasspathEntry setSourceEntry(IClasspathEntry e) {
		return new ClasspathEntry(e.getContentKind(), e.getEntryKind(), 
				featureProject.getBuildFolder().getFullPath(), e.getInclusionPatterns(), e.getExclusionPatterns(), 
				e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, 
				e.isExported(), e.getAccessRules(), e.combineAccessRules(), e.getExtraAttributes());
	}

	/**
	 * @return A default source entry
	 */
	public IClasspathEntry getSourceEntry() {
		return new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, 
				IClasspathEntry.CPE_SOURCE, featureProject.getBuildFolder().getFullPath(), new IPath[0],
				new IPath[0], null, null, null, false, null, false, new IClasspathAttribute[0]);
	}

	/**
	 * Replaces the composer of the given feature project by <code>AHEAD</code>.
	 * @param project 
	 */
	@Override
	void changeComposer(IFeatureProject project) {
		project.setComposerID(AheadComposer.COMPOSER_ID);
	}

	/**
	 * Replaces <code>original()</code> by <code>Super().methodName()</code>.<br>
	 * Inserts <code>refines</code> to classes that refine.
	 */
	@Override
	public String changeFile(String fileText, IFile file) {
		return changeFile(fileText, file, null);
	}
	
	// XXX private fields used in refining classes need to be set package private  
	private String changeFile(String fileText, IFile file, AbstractList<String> methodNames) {
		fileText = fileText.replaceFirst("package\\s[\\w,\\s,.]*;", ""); 
		
		if (fileText.contains("original(")) {
			// XXX also set refines if the file exists in a feature before
			fileText = fileText.replaceFirst(" class ",	" refines class ");
		}
		int i = 0;
		while (fileText.contains("original(")) {
			fileText = fileText.replaceFirst("original\\(", "Super()." + 
					(file != null ? getMethodName(getLine(fileText), file) : methodNames.get(i++)) + "(");
		}
		return fileText;
	}
	
	public String TChangeFile(String fileText, LinkedList<String> methodNames) {
		return changeFile(fileText, null, methodNames);
	}

	/**
	 * @param fileText 
	 * @return The lines of the given text
	 */
	private int getLine(String fileText) {
		return (fileText.substring(0, fileText.indexOf("original("))).split("\r\n").length;
	}

	/**
	 *
	 * @param line
	 * @param file
	 * @return The Method at the given line
	 */
	private String getMethodName(int line, IFile file) {
		if (model != null && model.getClass(file) !=  null) {
			FSTFeature[] features = model.getFeatures();
			LinkedList<FSTMethod> methods = new LinkedList<FSTMethod>();
			for (FSTFeature f : features) {
				for (FSTClass c : f.getClasses().values()) {
					if (c.getFile().getName().equals(file.getName())) {
						for (FSTMethod m : c.getMethods()) {
							methods.add(m);
						}
					}
				}
			}

			for (FSTMethod method : methods) {
				if (method.getBeginLine() <= line && method.getEndLine() >= line) {
					return method.getMethodName();
				}
			}
		}
		return "";
	}

	/**
	 * Replaces the file extension <code>.java</code> by <code>.jak</code> of the given file
	 * @param file
	 */
	@Override
	void replaceFileExtension(IFile file) {
		try {
			file.move(((IFolder)file.getParent()).getFile(file.getName().replace(".java", ".jak")).getFullPath(), true, null);
		} catch (CoreException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param fileExtension The file extension of a file
	 * @return <code>true</code> if java
	 */
	@Override
	boolean canConvert(String fileExtension) {
		return "java".equals(fileExtension);
	}

}
