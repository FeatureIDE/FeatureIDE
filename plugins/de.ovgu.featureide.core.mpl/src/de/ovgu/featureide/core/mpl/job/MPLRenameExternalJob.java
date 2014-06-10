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
package de.ovgu.featureide.core.mpl.job;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.refactoring.IJavaRefactorings;
import org.eclipse.jdt.core.refactoring.descriptors.MoveDescriptor;
import org.eclipse.jdt.core.refactoring.descriptors.RenameJavaElementDescriptor;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.ltk.core.refactoring.CheckConditionsOperation;
import org.eclipse.ltk.core.refactoring.PerformRefactoringOperation;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringContribution;
import org.eclipse.ltk.core.refactoring.RefactoringCore;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.job.util.AMonitorJob;

/**
 * 
 * @author Sebastian Krieter
 */
@SuppressWarnings("restriction")
public class MPLRenameExternalJob extends
		AMonitorJob<MPLRenameExternalJob.Arguments> {

	public static class Arguments extends AJobArguments {
		private final IProject externalProject;
		private final String prefix;

		public Arguments(IProject externalProject, String prefix) {
			super(Arguments.class);
			this.externalProject = externalProject;
			this.prefix = prefix;
		}
	}

	protected MPLRenameExternalJob(Arguments arguments) {
		super("Renaming Packages", arguments);
		setPriority(BUILD);
	}

	@Override
	protected boolean work() {
		JavaProject javaProject = new JavaProject(arguments.externalProject, null);
		IPackageFragmentRoot packageFragmentRoot;

		List<IPackageFragment> packages = new LinkedList<IPackageFragment>();
		try {
			IPackageFragmentRoot[] packageFragmentRoots = javaProject.getPackageFragmentRoots();
			packageFragmentRoot = packageFragmentRoots[0];
			IJavaElement[] fragments = packageFragmentRoot.getChildren();
			for (int j = 0; j < fragments.length; j++) {
				IPackageFragment fragment = (IPackageFragment) fragments[j];
				packages.add(fragment);
			}
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		ICompilationUnit[] defaultCompilationUnits = null;
		final Pattern p = Pattern.compile(arguments.prefix.replace(".", "\\.") + "(\\..*)?");
		
		Iterator<IPackageFragment> it = packages.iterator();
		while (it.hasNext()) {
			IPackageFragment pckg = it.next();
			if (pckg.isDefaultPackage()) {
				if (pckg.exists()) {
					try {
						defaultCompilationUnits = pckg.getCompilationUnits();
					} catch (JavaModelException e) {
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
		
		for (IPackageFragment pckg : packages) {
			if (!renamePackage(pckg)) {
				return false;
			}
		}

		try {
			arguments.externalProject.refreshLocal(IResource.DEPTH_INFINITE, monitor);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
		
		MPLPlugin.getDefault().logInfo("Packages renamed.");
		return true;
	}

	private boolean renamePackage(IPackageFragment pckg) {
		try {
			if (!pckg.containsJavaResources()) {
				return true;
			}
		} catch (JavaModelException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		RefactoringContribution contribution = RefactoringCore.getRefactoringContribution(IJavaRefactorings.RENAME_PACKAGE);
		RenameJavaElementDescriptor descriptor = (RenameJavaElementDescriptor) contribution.createDescriptor();
		descriptor.setProject(arguments.externalProject.getName());
		descriptor.setUpdateReferences(true);
		descriptor.setJavaElement(pckg);
		descriptor.setNewName(arguments.prefix + "." + pckg.getElementName());

		RefactoringStatus status = new RefactoringStatus();
		try {
			final NullProgressMonitor monitor = new NullProgressMonitor();
			Refactoring refactoring = descriptor.createRefactoring(status);
			new PerformRefactoringOperation(refactoring, CheckConditionsOperation.ALL_CONDITIONS).run(monitor);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}
	
	private boolean renameDefaultPackage(IPackageFragmentRoot packageFragmentRoot, ICompilationUnit[] compilationUnits) {
		if (compilationUnits != null && compilationUnits.length > 0) {
			RefactoringContribution contribution = RefactoringCore.getRefactoringContribution(IJavaRefactorings.MOVE);
			MoveDescriptor descriptor = (MoveDescriptor) contribution.createDescriptor();

			descriptor.setProject(arguments.externalProject.getName());
			descriptor.setDestination(packageFragmentRoot.getPackageFragment(arguments.prefix));			
			descriptor.setMoveResources(new IFile[0], new IFolder[0], compilationUnits);
			descriptor.setUpdateReferences(true);
			
			RefactoringStatus status = new RefactoringStatus();
			try {
				final NullProgressMonitor monitor = new NullProgressMonitor();
				Refactoring refactoring = descriptor.createRefactoring(status);
				new PerformRefactoringOperation(refactoring, CheckConditionsOperation.ALL_CONDITIONS).run(monitor);
			} catch (CoreException e) {
				MPLPlugin.getDefault().logError(e);
				return false;
			}
		}
		return true;
	}
}
