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
package de.ovgu.featureide.featurehouse.refactoring;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CheckConditionsOperation;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.PerformChangeOperation;
import org.eclipse.ltk.core.refactoring.PerformRefactoringOperation;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.UndoTextFileChange;
import org.eclipse.ltk.core.refactoring.resource.RenameResourceChange;
import org.eclipse.ui.dialogs.IOverwriteQuery;
import org.eclipse.ui.wizards.datatransfer.FileSystemStructureProvider;
import org.eclipse.ui.wizards.datatransfer.ImportOperation;
import org.junit.Before;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;

/**
 * TODO description
 * 
 * @author steffen
 */
public abstract class RenameRefactoringTest {

	protected IFeatureProject featureProject;
	private ProjectSignatures signatures;

	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final String path = workspace.getRoot().getLocation().toOSString();
		final IProjectDescription desc = workspace.loadProjectDescription(new Path(path + "/HelloWorld-FH-Java-Test/.project"));
		final IProject project = workspace.getRoot().getProject(desc.getName());
		if (!project.exists()) project.create(null);
		if (!project.isOpen()) project.open(null);
		CorePlugin.getDefault().addProject(project);
		featureProject = CorePlugin.getFeatureProjects().iterator().next();

		IOverwriteQuery overwriteQuery = new IOverwriteQuery() {

			public String queryOverwrite(String file) {
				return ALL;
			}
		};

		project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());

		String baseDir = path + "/HelloWorld-FH-Java-Test";// location of files to import""

		ImportOperation importOperation = new ImportOperation(project.getFullPath(), new File(baseDir), FileSystemStructureProvider.INSTANCE, overwriteQuery);
		importOperation.setCreateContainerStructure(false);
		importOperation.run(new NullProgressMonitor());

		project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());

		ExtendedFujiSignaturesJob efsj = new ExtendedFujiSignaturesJob(featureProject);
		efsj.schedule();
		efsj.join();

		signatures = featureProject.getFSTModel().getProjectSignatures();
	}

	protected Set<Integer> hashCodeOfChanges(final String fullOldName, final String newName, final RefactoringStatus status) throws Exception {

		RenameRefactoring<?> refactoring = getRefactoring(fullOldName);
		refactoring.setNewName(newName);
		CompositeChange undoChanges = null;
		IProgressMonitor monitor = new NullProgressMonitor();
		Set<Integer> result = new HashSet<>();
		try {
//			status.merge(refactoring.checkAllConditions(monitor));
//			if (status.hasError()) return result;

			PerformRefactoringOperation op = new PerformRefactoringOperation(refactoring, CheckConditionsOperation.ALL_CONDITIONS);
			op.run(monitor);
			undoChanges = (CompositeChange) op.getUndoChange();
			status.merge(op.getConditionStatus());
			if (status.hasError()) return result;

			CompositeChange child = (CompositeChange) undoChanges.getChildren()[0];

			for (Change change : child.getChildren()) {
				if (change instanceof RenameResourceChange) {
					RenameResourceChange resourceChange = (RenameResourceChange) change;
					result.add(getHashCodeOfFile((IFile) resourceChange.getModifiedElement()));
				} else if (change instanceof UndoTextFileChange) {
					UndoTextFileChange textFileChange = (UndoTextFileChange) change;
					final IFile modifiedElement = (IFile) textFileChange.getModifiedElement();
					if (modifiedElement.exists()) result.add(getHashCodeOfFile(modifiedElement));
				}
			}
		} finally {
			// undo-action
			if (undoChanges != null) new PerformChangeOperation(undoChanges).run(monitor);
		}

		return result;
	}

	protected int getHashCodeOfFile(final IFile file) throws CoreException, IOException {
		final InputStream contents = file.getContents();
		byte[] contentsArray = new byte[contents.available()];
		contents.read(contentsArray);
		return new String(contentsArray).hashCode();
	}

	protected AbstractSignature getNamedSignature(final String fullSigName) {
		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (checkSignature(signature, fullSigName)) {
				return signature;
			}
		}
		return null;
	}

	protected boolean checkSignature(final AbstractSignature signature, final String fullSigName) {
		return signature.getFullName().equals(fullSigName) && hasSameType(signature); // && ((FujiMethodSignature) signature).getParameterTypes().isEmpty();
	}

	protected abstract boolean hasSameType(final AbstractSignature signature);

	protected abstract RenameRefactoring<?> getRefactoring(final String fullSigName);
}
