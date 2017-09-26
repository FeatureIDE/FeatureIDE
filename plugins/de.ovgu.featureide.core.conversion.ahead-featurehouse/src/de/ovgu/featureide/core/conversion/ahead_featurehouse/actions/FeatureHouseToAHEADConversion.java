/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.conversion.ahead_featurehouse.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_COMPOSER_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHANGE_THE_COMPOSER_OF_PROJECT;
import static de.ovgu.featureide.fm.core.localization.StringTable.FROM_FEATUREHOUSE_TO_AHEAD_;
import static de.ovgu.featureide.fm.core.localization.StringTable.REPLACE_KEYWORDS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

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
import de.ovgu.featureide.core.conversion.ahead_featurehouse.ConversionPlugin;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;

/**
 * Changes the composer of an feature project project to <code>AHEAD</code>.
 *
 * @author Jens Meinicke
 */
@SuppressWarnings(RESTRICTION)
public class FeatureHouseToAHEADConversion extends ComposerConversion {

	private FSTModel model;

	/**
	 * Changes the composer of the given feature project to <code>AHEAD</code>.
	 *
	 * @param featureProject
	 */
	public FeatureHouseToAHEADConversion(final IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		this.featureProject = featureProject;
		ConversionPlugin.getDefault().logInfo(CHANGE_THE_COMPOSER_OF_PROJECT + featureProject.getProjectName() + FROM_FEATUREHOUSE_TO_AHEAD_);
		final Job job = new Job(CHANGE_COMPOSER_) {

			@Override
			protected IStatus run(IProgressMonitor monitor) {
				try {
					setJavaBuildPath(featureProject);
					monitor.beginTask(CHANGE_COMPOSER_, 2);
					monitor.subTask("Build full FSTModel.");
					buildFullFSTModel();
					model = featureProject.getFSTModel();
					monitor.worked(1);
					monitor.subTask(REPLACE_KEYWORDS_);
					startProjectConversion(featureProject);
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
	 *
	 * @param featureProject
	 */
	private void setJavaBuildPath(IFeatureProject featureProject) {
		try {
			final JavaProject javaProject = new JavaProject(featureProject.getProject(), null);
			final IClasspathEntry[] classpathEntries = javaProject.getRawClasspath();
			for (int i = 0; i < classpathEntries.length; i++) {
				/** change the actual source entry **/
				if (classpathEntries[i].getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					classpathEntries[i] = setSourceEntry(classpathEntries[i]);
					javaProject.setRawClasspath(classpathEntries, null);
					return;
				}
			}

			/** case: no source entry **/
			final IClasspathEntry[] newEntries = new IClasspathEntry[classpathEntries.length + 1];
			System.arraycopy(classpathEntries, 0, newEntries, 0, classpathEntries.length);
			newEntries[newEntries.length - 1] = getSourceEntry();
			javaProject.setRawClasspath(classpathEntries, null);
		} catch (final JavaModelException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Set the source path of given <code>ClasspathEntry</code> to the current build path
	 *
	 * @param e The entry to set
	 * @return The entry with the new source path
	 */
	public IClasspathEntry setSourceEntry(IClasspathEntry e) {
		return new ClasspathEntry(e.getContentKind(), e.getEntryKind(), featureProject.getBuildFolder().getFullPath(), e.getInclusionPatterns(),
				e.getExclusionPatterns(), e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, e.isExported(), e.getAccessRules(),
				e.combineAccessRules(), e.getExtraAttributes());
	}

	/**
	 * @return A default source entry
	 */
	public IClasspathEntry getSourceEntry() {
		return new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, IClasspathEntry.CPE_SOURCE, featureProject.getBuildFolder().getFullPath(), new IPath[0],
				new IPath[0], null, null, null, false, null, false, new IClasspathAttribute[0]);
	}

	/**
	 * Replaces the composer of the given feature project by <code>AHEAD</code>.
	 *
	 * @param project
	 */
	@Override
	void changeComposer(IFeatureProject project) {
		project.setComposerID(AheadComposer.COMPOSER_ID);
	}

	/**
	 * Replaces <code>original()</code> by <code>Super().methodName()</code>.<br> Inserts <code>refines</code> to classes that refine.
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
			fileText = fileText.replaceFirst(" class ", " refines class ");
		}
		int i = 0;
		while (fileText.contains("original(")) {
			fileText = fileText.replaceFirst("original\\(", "Super()." + (file != null ? getMethodName(getLine(fileText), file) : methodNames.get(i++)) + "(");
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
	 * @return The Method at the given line
	 */
	private String getMethodName(int line, IFile file) {
		if (model != null) {
			final String name = model.getAbsoluteClassName(file);
			if (model.getClass(name) != null) {
				final LinkedList<FSTMethod> methods = new LinkedList<FSTMethod>();
				for (final FSTRole role : model.getClass(name).getRoles()) {
					methods.addAll(role.getClassFragment().getMethods());
				}
				for (final FSTMethod method : methods) {
					if ((method.getLine() <= line) && (method.getEndLine() >= line)) {
						return method.getName();
					}
				}
			}
		}
		return "";
	}

	/**
	 * Replaces the file extension <code>.java</code> by <code>.jak</code> of the given file
	 *
	 * @param file
	 */
	@Override
	void replaceFileExtension(IFile file) {
		try {
			file.move(((IFolder) file.getParent()).getFile(file.getName().replace(".java", ".jak")).getFullPath(), true, null);
		} catch (final CoreException e) {
			ConversionPlugin.getDefault().logError(e);
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
