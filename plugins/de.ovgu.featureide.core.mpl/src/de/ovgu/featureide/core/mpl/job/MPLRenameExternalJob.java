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

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.refactoring.IJavaRefactorings;
import org.eclipse.jdt.core.refactoring.descriptors.RenameJavaElementDescriptor;
import org.eclipse.jdt.internal.core.JavaProject;
import org.eclipse.ltk.core.refactoring.Change;
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

		List<IPackageFragment> packages = new LinkedList<IPackageFragment>();
		try {
			IPackageFragmentRoot[] packageFragmentRoots = javaProject.getPackageFragmentRoots();
			IPackageFragmentRoot packageFragmentRoot = packageFragmentRoots[0];
			IJavaElement[] fragments = packageFragmentRoot.getChildren();
			for (int j = 0; j < fragments.length; j++) {
				IPackageFragment fragment = (IPackageFragment) fragments[j];
				packages.add(fragment);
			}
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		Iterator<IPackageFragment> it = packages.iterator();
		while (it.hasNext()) {
			IPackageFragment pckg = it.next();
			if (pckg.isDefaultPackage()) {
				it.remove();
			} else if (pckg.getElementName().startsWith(arguments.prefix)) {
				if (!renamePackage(pckg)) {
					return false;
				}
				it.remove();
			}
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

	private boolean renamePackage(IJavaElement pckg) {
		RefactoringContribution contribution = RefactoringCore.getRefactoringContribution(IJavaRefactorings.RENAME_PACKAGE);
		RenameJavaElementDescriptor descriptor = (RenameJavaElementDescriptor) contribution.createDescriptor();
		descriptor.setProject(arguments.externalProject.getName());
		descriptor.setUpdateReferences(true);
		descriptor.setJavaElement(pckg);
		descriptor.setNewName(arguments.prefix + pckg.getElementName());

		RefactoringStatus status = new RefactoringStatus();
		try {
			final NullProgressMonitor monitor = new NullProgressMonitor();
			Refactoring refactoring = descriptor.createRefactoring(status);
			refactoring.checkAllConditions(monitor);
			Change change = refactoring.createChange(monitor);
			change.perform(monitor);

		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}
}
