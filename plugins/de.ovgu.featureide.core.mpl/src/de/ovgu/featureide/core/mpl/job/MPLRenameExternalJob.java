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
package de.ovgu.featureide.core.mpl.job;

import static de.ovgu.featureide.fm.core.localization.StringTable.PACKAGES_RENAMED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.RENAMING_PACKAGES;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.IClasspathAttribute;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.refactoring.IJavaRefactorings;
import org.eclipse.jdt.core.refactoring.descriptors.MoveDescriptor;
import org.eclipse.jdt.core.refactoring.descriptors.RenameJavaElementDescriptor;
import org.eclipse.jdt.internal.core.ClasspathEntry;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.ltk.core.refactoring.CheckConditionsOperation;
import org.eclipse.ltk.core.refactoring.PerformRefactoringOperation;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringContribution;
import org.eclipse.ltk.core.refactoring.RefactoringCore;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 *
 * @author Sebastian Krieter
 */
@SuppressWarnings(RESTRICTION)
public class MPLRenameExternalJob extends AProjectJob<MPLRenameExternalJob.Arguments, Boolean> {

	public static class Arguments extends JobArguments {

		private final IProject externalProject;
		private final String prefix;
		private final IPath srcPath;

		public Arguments(IProject externalProject, String prefix, IPath srcPath) {
			super(Arguments.class);
			this.externalProject = externalProject;
			this.prefix = prefix;
			this.srcPath = srcPath;
		}
	}

	protected MPLRenameExternalJob(Arguments arguments) {
		super(RENAMING_PACKAGES, arguments);
		javaProject = new JavaProject(arguments.externalProject, null);
	}

	private static int getJavaBuildPathEntry(JavaProject javaProject) {
		try {
			final IClasspathEntry[] classpathEntrys = javaProject.getRawClasspath();

			for (int i = 0; i < classpathEntrys.length; ++i) {
				if (classpathEntrys[i].getEntryKind() == IClasspathEntry.CPE_SOURCE) {
					return i;
				}
			}
		} catch (final JavaModelException e) {
			MPLPlugin.getDefault().logError(e);
		}
		return -1;
	}

	private static IPath setJavaBuildPath(JavaProject javaProject, IPath path, int index) {
		try {
			final IClasspathEntry[] classpathEntrys = javaProject.getRawClasspath();

			if (index >= 0) {
				final IClasspathEntry e = classpathEntrys[index];
				if (!e.getPath().equals(path)) {
					final IPath formerSourcePath = e.getPath();
					classpathEntrys[index] = new ClasspathEntry(e.getContentKind(), e.getEntryKind(), path, e.getInclusionPatterns(), e.getExclusionPatterns(),
							e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, e.isExported(), e.getAccessRules(), e.combineAccessRules(),
							e.getExtraAttributes());
					javaProject.setRawClasspath(classpathEntrys, null);
					return formerSourcePath;
				}
			} else {
				final IClasspathEntry[] newEntrys = new IClasspathEntry[classpathEntrys.length + 1];
				System.arraycopy(classpathEntrys, 0, newEntrys, 0, classpathEntrys.length);
				newEntrys[newEntrys.length - 1] = new ClasspathEntry(IPackageFragmentRoot.K_SOURCE, IClasspathEntry.CPE_SOURCE, path, new IPath[0],
						new IPath[0], null, null, null, false, null, false, new IClasspathAttribute[0]);
				javaProject.setRawClasspath(newEntrys, null);
			}
		} catch (final JavaModelException e) {
			MPLPlugin.getDefault().logError(e);
		}

		return null;
	}

	public static void setJavaBuildPath(IProject project, IPath path) {
		final JavaProject javaProject = new JavaProject(project, null);
		setJavaBuildPath(javaProject, path, getJavaBuildPathEntry(javaProject));
	}

	private static void resetJavaBuildPath(JavaProject javaProject, IPath formerSourcePath, int formerSourcePathIndex) {
		try {
			final IClasspathEntry[] classpathEntrys = javaProject.getRawClasspath();

			if (formerSourcePath != null) {
				final IClasspathEntry e = classpathEntrys[formerSourcePathIndex];
				classpathEntrys[formerSourcePathIndex] = new ClasspathEntry(e.getContentKind(), e.getEntryKind(), formerSourcePath, e.getInclusionPatterns(),
						e.getExclusionPatterns(), e.getSourceAttachmentPath(), e.getSourceAttachmentRootPath(), null, e.isExported(), e.getAccessRules(),
						e.combineAccessRules(), e.getExtraAttributes());
				javaProject.setRawClasspath(classpathEntrys, null);
			} else if (formerSourcePathIndex == -1) {
				final IClasspathEntry[] newEntrys = new IClasspathEntry[classpathEntrys.length - 1];
				System.arraycopy(classpathEntrys, 0, newEntrys, 0, newEntrys.length);
				javaProject.setRawClasspath(newEntrys, null);
			}
		} catch (final JavaModelException e) {
			MPLPlugin.getDefault().logError(e);
		}
	}

	private int formerSourcePathIndex = -1;
	private IPath formerSourcePath = null;
	private final JavaProject javaProject;

	@Override
	public Boolean execute(IMonitor workMonitor) throws Exception {
		try {
			this.workMonitor = workMonitor;
			formerSourcePathIndex = getJavaBuildPathEntry(javaProject);
			formerSourcePath = setJavaBuildPath(javaProject, arguments.srcPath, formerSourcePathIndex);
		} finally {
			resetJavaBuildPath(javaProject, formerSourcePath, formerSourcePathIndex);
		}
		return renameProject();
	}

	private boolean renameProject() {
		final IPackageFragmentRoot packageFragmentRoot;

		final List<IPackageFragment> packages = new LinkedList<IPackageFragment>();
		try {
			final IPackageFragmentRoot[] packageFragmentRoots = javaProject.getPackageFragmentRoots();
			packageFragmentRoot = packageFragmentRoots[0];
			final IJavaElement[] fragments = packageFragmentRoot.getChildren();
			for (int j = 0; j < fragments.length; j++) {
				final IPackageFragment fragment = (IPackageFragment) fragments[j];
				packages.add(fragment);
			}
		} catch (final Exception e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		ICompilationUnit[] defaultCompilationUnits = null;
		final Pattern p = Pattern.compile(arguments.prefix.replace(".", "\\.") + "(\\..*)?");

		final Iterator<IPackageFragment> it = packages.iterator();
		while (it.hasNext()) {
			final IPackageFragment pckg = it.next();
			if (pckg.isDefaultPackage()) {
				if (pckg.exists()) {
					try {
						defaultCompilationUnits = pckg.getCompilationUnits();
					} catch (final JavaModelException e) {
						MPLPlugin.getDefault().logError(e);
						return false;
					}
				}
				it.remove();
			} else if (p.matcher(pckg.getElementName()).matches()) {
				if (!renamePackage(pckg)) {
					return false;
				}
				it.remove();
			}
		}

		if (!renameDefaultPackage(packageFragmentRoot, defaultCompilationUnits)) {
			return false;
		}

		for (final IPackageFragment pckg : packages) {
			if (!renamePackage(pckg)) {
				return false;
			}
		}

		try {
			arguments.externalProject.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
		MPLPlugin.getDefault().logInfo(PACKAGES_RENAMED_);
		return true;
	}

	private boolean renamePackage(IPackageFragment pckg) {
		try {
			if (!pckg.containsJavaResources()) {
				return true;
			}
		} catch (final JavaModelException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		final RefactoringContribution contribution = RefactoringCore.getRefactoringContribution(IJavaRefactorings.RENAME_PACKAGE);
		final RenameJavaElementDescriptor descriptor = (RenameJavaElementDescriptor) contribution.createDescriptor();
		descriptor.setProject(arguments.externalProject.getName());
		descriptor.setUpdateReferences(true);
		descriptor.setJavaElement(pckg);
		descriptor.setNewName(arguments.prefix + "." + pckg.getElementName());

		final RefactoringStatus status = new RefactoringStatus();
		try {
			final NullProgressMonitor monitor = new NullProgressMonitor();
			final Refactoring refactoring = descriptor.createRefactoring(status);
			new PerformRefactoringOperation(refactoring, CheckConditionsOperation.ALL_CONDITIONS).run(monitor);
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	private boolean renameDefaultPackage(IPackageFragmentRoot packageFragmentRoot, ICompilationUnit[] compilationUnits) {
		if ((compilationUnits != null) && (compilationUnits.length > 0)) {
			final RefactoringContribution contribution = RefactoringCore.getRefactoringContribution(IJavaRefactorings.MOVE);
			final MoveDescriptor descriptor = (MoveDescriptor) contribution.createDescriptor();

			descriptor.setProject(arguments.externalProject.getName());
			descriptor.setDestination(packageFragmentRoot.getPackageFragment(arguments.prefix));
			descriptor.setMoveResources(new IFile[0], new IFolder[0], compilationUnits);
			descriptor.setUpdateReferences(true);

			final RefactoringStatus status = new RefactoringStatus();
			try {
				final NullProgressMonitor monitor = new NullProgressMonitor();
				final Refactoring refactoring = descriptor.createRefactoring(status);
				new PerformRefactoringOperation(refactoring, CheckConditionsOperation.ALL_CONDITIONS).run(monitor);
			} catch (final CoreException e) {
				MPLPlugin.getDefault().logError(e);
				return false;
			}
		}
		return true;
	}

}
