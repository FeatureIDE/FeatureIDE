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
package de.ovgu.featureide.featurehouse.refactoring;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.viewsupport.BasicElementLabels;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.resource.RenameResourceChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.ExtendedSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.refactoring.matcher.FieldSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.LocalVariableSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.MethodSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.TypeSignatureMatcher;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public abstract class RenameRefactoring<T extends AbstractSignature> extends Refactoring {

	private final IFeatureProject featureProject;
	protected final T renamingElement;
	protected String newName;
	protected final String file;
	private List<Change> changes;

	public RenameRefactoring(T selection, IFeatureProject featureProject, String file) {
		this.renamingElement = selection;
		this.featureProject = featureProject;
		this.newName = renamingElement.getName();
		this.file = file;
	}

	public void setNewName(String newName) {
		this.newName = newName;
	}

	public String getNewName() {
		return this.newName;
	}

	protected abstract RefactoringStatus checkNewElementName(String newName) throws CoreException;

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		return checkIfCuBroken();
	}

	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException, CoreException {

		refactoringStatus.merge(checkNewElementName(newName));
		if (refactoringStatus.hasFatalError()) return;
		refactoringStatus.merge(checkIfCuBroken());
		if (refactoringStatus.hasFatalError()) return;
	}

	@Override
	public final RefactoringStatus checkFinalConditions(final IProgressMonitor pm) throws CoreException, OperationCanceledException {
		final RefactoringStatus refactoringStatus = new RefactoringStatus();

		try {
			pm.beginTask("Checking preconditions...", 2);

			changes = new ArrayList<Change>();

			pm.setTaskName(RefactoringCoreMessages.RenameMethodRefactoring_taskName_checkingPreconditions);

			SignatureMatcher matcher = null;
			if (renamingElement instanceof FujiMethodSignature)
				matcher = new MethodSignatureMatcher(featureProject.getProjectSignatures(), renamingElement, newName);
			else if (renamingElement instanceof FujiClassSignature)
				matcher = new TypeSignatureMatcher(featureProject.getProjectSignatures(), renamingElement, newName);
			else if (renamingElement instanceof FujiFieldSignature)
				matcher = new FieldSignatureMatcher(featureProject.getProjectSignatures(), renamingElement, newName);
			else if (renamingElement instanceof FujiLocalVariableSignature)
				matcher = new LocalVariableSignatureMatcher(featureProject.getProjectSignatures(), renamingElement, newName);

			if (matcher == null) return refactoringStatus;

			matcher.findMatchedSignatures();

			if (matcher.getSelectedSignature() == null) return refactoringStatus;

			checkPreConditions(matcher, refactoringStatus);
			if (refactoringStatus.hasFatalError()) return refactoringStatus;

			for (RefactoringSignature refactoringSignature : createRefactoringSignatures(matcher)) {
				refactoringStatus.merge(createChanges(refactoringSignature));
			}

		} finally {
			pm.done();
		}
		return refactoringStatus;
	}

	private Set<RefactoringSignature> createRefactoringSignatures(final SignatureMatcher matcher) {
		Set<RefactoringSignature> result = new HashSet<>();

		AbstractSignature selectedSignature = matcher.getSelectedSignature();
		for (AbstractSignature matchedSignature : matcher.getMatchedSignatures()) {

			if ((selectedSignature instanceof FujiClassSignature && selectedSignature.equals(matchedSignature))
				|| !(selectedSignature instanceof FujiClassSignature)) handleInvokedSignatureOfMatchedSignature(result, matchedSignature);

			final FOPFeatureData[] featureData = (FOPFeatureData[]) matchedSignature.getFeatureData();
			for (int j = 0; j < featureData.length; j++) {
				final FOPFeatureData fopFeature = featureData[j];

				final AbstractSignature declaration;
				if (selectedSignature instanceof FujiClassSignature) declaration = selectedSignature;
				else declaration = matchedSignature;

				final String absoluteFilePath = fopFeature.getAbsoluteFilePath();
				RefactoringSignature signature = getRefactoringSignature(result, absoluteFilePath);
				if (signature == null) signature = new RefactoringSignature(absoluteFilePath, declaration);

				signature.addPosition(fopFeature.getSigPosition());
				result.add(signature);
			}
		}

		return result;
	}

	private void handleInvokedSignatureOfMatchedSignature(final Set<RefactoringSignature> result, final AbstractSignature matchedSignature) {

		for (ExtendedSignature invokedSignature : matchedSignature.getInvocationSignatures()) {
			for (AFeatureData featureData : invokedSignature.getSig().getFeatureData()) {
				if (featureData.getID() == invokedSignature.getFeatureID()) {
					final String absolutePath = featureData.getAbsoluteFilePath();
					RefactoringSignature signature = getRefactoringSignature(result, absolutePath);
					if (signature == null) {
						signature = new RefactoringSignature(absolutePath, matchedSignature);
						result.add(signature);
					}
					signature.addPosition(invokedSignature.getPosition());
					break;
				}
			}
		}
	}

	private RefactoringSignature getRefactoringSignature(final Set<RefactoringSignature> result, final String relativePath) {
		for (RefactoringSignature refactoringSignature : result) {
			if (refactoringSignature.getAbsolutePathToFile().equals(relativePath)) return refactoringSignature;
		}
		return null;
	}

	protected String getFullFilePath(final String relativePath) {
		String fileName = RefactoringUtil.getFile(relativePath).getFullPath().toString();
		if (fileName.startsWith(File.separator)) fileName = fileName.substring(1);
		return fileName;
	}

	@Override
	public final Change createChange(IProgressMonitor pm) throws CoreException, OperationCanceledException {

		try {
			pm.beginTask("Creating change...", 1);

			return new CompositeChange(getName(), changes.toArray(new Change[changes.size()]));
		} finally {
			pm.done();
		}
	}

	private RefactoringStatus createChanges(final RefactoringSignature refactoringSig) {

		RefactoringStatus status = new RefactoringStatus();
		MultiTextEdit multiEdit = new MultiTextEdit();

		if (refactoringSig.getPositions().isEmpty()) return status;

		IFile ifile = RefactoringUtil.getFile(refactoringSig.getAbsolutePathToFile());

		IDocumentProvider provider = new TextFileDocumentProvider();
		try {
			provider.connect(ifile);
			final IDocument doc = provider.getDocument(ifile);

			for (SignaturePosition position : refactoringSig.getPositions()) {
				int offset = doc.getLineOffset(position.getStartRow() - 1) + position.getIdentifierStart() - 1;
				final int length = position.getIdentifierEnd() - position.getIdentifierStart() + 1;
				multiEdit.addChild(new ReplaceEdit(offset, length, newName));
			}

		} catch (CoreException e) {
			e.printStackTrace();
		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		TextFileChange change = new TextFileChange(JavaCore.removeJavaLikeExtension(ifile.getName()), ifile);
		change.initializeValidationData(null);
		change.setTextType("java");
		change.setEdit(multiEdit);
		changes.add(change);

		if (willRenameCU(refactoringSig, status)) {
			String filePath = File.separator + ifile.getProject().getName() + File.separator + ifile.getProjectRelativePath();
			RenameResourceChange resourceChange = new RenameResourceChange(new Path(filePath), newName + ".java");
			resourceChange.initializeValidationData(null);
			changes.add(resourceChange);
		}
		return status;
	}

	private boolean willRenameCU(final RefactoringSignature refactoringSig, final RefactoringStatus status) {
		final AbstractSignature signature = refactoringSig.getDeclaration();
		if (!(signature instanceof AbstractClassSignature)) return false;
		if (!checkIfRenamingType(signature, refactoringSig.getAbsolutePathToFile())) return false;
		String name = JavaCore.removeJavaLikeExtension(signature.getName());
		if (!((signature.getParent() == null) && name.equals(signature.getName()))) return false;
		status.merge(checkNewPathValidity(refactoringSig.getAbsolutePathToFile()));
		if (status.hasError()) return false;
		status.merge(existCompilationUnitNewName(refactoringSig.getAbsolutePathToFile()));
		if (status.hasError()) return false;
		return true;
	}

	private RefactoringStatus existCompilationUnitNewName(final String file) {
		IPath renamedResourcePath = RefactoringUtil.getFile(file).getParent().getFullPath();
		if (Checks.resourceExists(renamedResourcePath.append(newName + ".java"))) return RefactoringStatus
				.createFatalErrorStatus(Messages.format(RefactoringCoreMessages.Checks_cu_name_used, BasicElementLabels.getResourceName(newName)));
		else return new RefactoringStatus();
	}

	private boolean checkIfRenamingType(final AbstractSignature selectedSignature, final String file) {
		for (AFeatureData featureData : selectedSignature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(file)) return true;
		}
		return false;
	}

	protected RefactoringStatus checkIfCuBroken() throws JavaModelException {
		ICompilationUnit cu = RefactoringUtil.getCompilationUnit(file);
		if (cu == null) return RefactoringStatus.createFatalErrorStatus(RefactoringCoreMessages.Checks_cu_not_created);
		else if (!cu.isStructureKnown()) return RefactoringStatus.createFatalErrorStatus(RefactoringCoreMessages.Checks_cu_not_parsed);

		return new RefactoringStatus();
	}

	protected String getFullFilePathForRenamingElement() {
		return getFullFilePath(renamingElement.getFirstFeatureData().getAbsoluteFilePath());
	}

	protected String[] getSourceComplianceLevels() {
		String[] sourceComplianceLevels = new String[] { JavaCore.getOption(JavaCore.COMPILER_SOURCE), JavaCore.getOption(JavaCore.COMPILER_COMPLIANCE) };
		return sourceComplianceLevels;
	}

	private RefactoringStatus checkNewPathValidity(final String file) {
		ICompilationUnit unit = RefactoringUtil.getCompilationUnit(file);
		IContainer c = unit.getResource().getParent();

		String notRename = RefactoringCoreMessages.RenameTypeRefactoring_will_not_rename;
		IStatus status = c.getWorkspace().validateName(newName, IResource.FILE);
		if (status.getSeverity() == IStatus.ERROR) return RefactoringStatus.createWarningStatus(status.getMessage() + ". " + notRename); //$NON-NLS-1$

		status = c.getWorkspace().validatePath(createNewPath(unit, newName), IResource.FILE);
		if (status.getSeverity() == IStatus.ERROR) return RefactoringStatus.createWarningStatus(status.getMessage() + ". " + notRename); //$NON-NLS-1$

		return new RefactoringStatus();
	}

	private String createNewPath(final ICompilationUnit unit, final String newName) {
		return unit.getResource().getFullPath().removeLastSegments(1).append(newName).toString();
	}
}
