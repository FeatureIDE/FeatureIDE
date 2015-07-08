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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
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
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.resource.RenameResourceChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.featurehouse.refactoring.matcher.FieldSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.LocalVariableSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.MethodSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.TypeSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.visitors.IASTVisitor;
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

	protected final IFeatureProject featureProject;
	protected final T renamingElement;
	protected ProjectSignatures signatures;
	protected String newName;
	private List<Change> changes;
	protected Map<String, AbstractClassSignature> classes = new HashMap<>();
	private Map<String, List<SearchMatch>> nodes = new HashMap<>();

	public RenameRefactoring(T selection, IFeatureProject featureProject) {
		this.renamingElement = selection;
		this.featureProject = featureProject;
		this.newName = renamingElement.getName();
	}

	public void setNewName(String newName) {
		this.newName = newName;
	}

	public String getNewName() {
		return this.newName;
	}

	protected abstract IASTVisitor getASTVisitor(final RefactoringSignature refactoringSignature, final String newName);

	protected abstract RefactoringStatus checkNewElementName(String newName) throws CoreException;
	
	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		return checkIfCuBroken();
	}

	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException, CoreException {

		refactoringStatus.merge(checkNewElementName(newName));
		if (refactoringStatus.hasFatalError())
			return;
		refactoringStatus.merge(checkIfCuBroken());
		if (refactoringStatus.hasFatalError())
			return;
	}
	
	@Override
	public final RefactoringStatus checkFinalConditions(final IProgressMonitor pm) throws CoreException, OperationCanceledException {
		final RefactoringStatus refactoringStatus = new RefactoringStatus();
		
		try {
			pm.beginTask("Checking preconditions...", 2);

			ExtendedFujiSignaturesJob efsj = new ExtendedFujiSignaturesJob(featureProject);
			efsj.schedule();
			efsj.join();

			changes = new ArrayList<Change>();

			signatures = featureProject.getFSTModel().getProjectSignatures();
			//TODO: Fehlermeldung
			if (signatures == null)
				return refactoringStatus;
			
			pm.setTaskName(RefactoringCoreMessages.RenameMethodRefactoring_taskName_checkingPreconditions);
			
			SignatureMatcher matcher = null;
			if (renamingElement instanceof FujiMethodSignature)
				matcher = new MethodSignatureMatcher(signatures, renamingElement, newName);
			else if (renamingElement instanceof FujiClassSignature)
				matcher = new TypeSignatureMatcher(signatures, renamingElement, newName);
			else if (renamingElement instanceof FujiFieldSignature)
				matcher = new FieldSignatureMatcher(signatures, renamingElement, newName);
			else if (renamingElement instanceof FujiLocalVariableSignature)
				matcher = new LocalVariableSignatureMatcher(signatures, renamingElement, newName);
			
			if (matcher == null)
				return refactoringStatus;
			
			matcher.findMatchedSignatures();
			
			if (matcher.getSelectedSignature() == null) 
				return refactoringStatus;
			
			checkPreConditions(matcher, refactoringStatus);
			if (refactoringStatus.hasFatalError()) 
				return refactoringStatus;
			
			for (RefactoringSignature refactoringSignature : createRefactoringSignatures(matcher)) {
				refactoringStatus.merge(search(refactoringSignature));
			}

			for (Entry<String, List<SearchMatch>> searchMatches : nodes.entrySet()) {
				rewriteAST(searchMatches.getKey(), searchMatches.getValue());
			}

		} catch (InterruptedException e) {
			e.printStackTrace();
		} finally {
			pm.done();
		}
		return refactoringStatus;
	}

	private Set<RefactoringSignature> createRefactoringSignatures(final SignatureMatcher matcher) {
		Set<RefactoringSignature> result = new HashSet<>();

		for (AbstractSignature matchedSignature : matcher.getMatchedSignatures()) {
			
			handleInvokedSignatureOfMatchedSignature(result, matchedSignature, (FOPFeatureData[]) matchedSignature.getFeatureData());
			
			final FOPFeatureData[] featureData = (FOPFeatureData[]) matchedSignature.getFeatureData();
			for (int j = 0; j < featureData.length; j++) {
				final FOPFeatureData fopFeature = featureData[j];

				addToRefactoringSignatures(result, matchedSignature, fopFeature.getAbsoluteFilePath());
			}
		}

		return result;
	}

	private void addToRefactoringSignatures(final Set<RefactoringSignature> result, final AbstractSignature matchedSignature, final String relativePath) {
		RefactoringSignature signature = getRefactoringSignature(result, relativePath);
		if (signature == null) {
			signature = new RefactoringSignature(relativePath, matchedSignature);
			result.add(signature);
		} else if (signature.getDeclaration() == null) {
			signature.setDeclaration(matchedSignature);
		}
		signature.setRenameDeclaration(true);
	}

	private void handleInvokedSignatureOfMatchedSignature(final Set<RefactoringSignature> result, final AbstractSignature matchedSignature, final FOPFeatureData[] fopFeatureData)  {

		for (FOPFeatureData featureData : fopFeatureData) {

			for (AbstractSignature invokedSignature : featureData.getInvokedSignatures()) {
				final FOPFeatureData[] invokedFeatureData = (FOPFeatureData[]) invokedSignature.getFeatureData();
				for (int i = 0; i < invokedFeatureData.length; i++) {
					final FOPFeatureData fopFeature = invokedFeatureData[i];

					final String absolutePath = fopFeature.getAbsoluteFilePath();
					RefactoringSignature signature = getRefactoringSignature(result, absolutePath);
					if (signature == null) {
						signature = new RefactoringSignature(absolutePath, matchedSignature);
						result.add(signature);
					}

					signature.addInvocation(invokedSignature);
				}
			}
		}
	}

	private RefactoringSignature getRefactoringSignature(final Set<RefactoringSignature> result, final String relativePath) {
		for (RefactoringSignature refactoringSignature : result) {
			if (refactoringSignature.getRelativePathToFile().equals(relativePath))
				return refactoringSignature;
		}
		return null;
	}

	private RefactoringStatus search(final RefactoringSignature refactoringSignatures) {

		final RefactoringStatus status = new RefactoringStatus();

		IASTVisitor visitor = getASTVisitor(refactoringSignatures, newName);
		visitor.startVisit();

		nodes.put(refactoringSignatures.getRelativePathToFile(), visitor.getMatches());
		
		for (String errorMsg : visitor.getErrors()) {
			status.addError(errorMsg);
		}
		return status;
	}

	protected IFile getFile(final String relativePath) {
		final IPath projectPath = ResourcesPlugin.getWorkspace().getRoot().getProject(featureProject.getProjectName()).getFullPath();
		
		int index = relativePath.lastIndexOf(projectPath.toString());
		String path = relativePath.substring(index);
		
		final IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(path));
		return file;
	}
	
	protected String getFullFilePath(final String relativePath) {
		String fileName = getFile(relativePath).getFullPath().toString();
		if (fileName.startsWith("/"))
			fileName = fileName.substring(1);
		return fileName;
	}
	
	protected ICompilationUnit getCompilationUnit(final String relativePath)
	{
		final IFile file = getFile(relativePath);
		
		if ((file == null) || ((file != null) && !file.isAccessible()))
			return null;

		return JavaCore.createCompilationUnitFrom(file);
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

	private void rewriteAST(String file, List<SearchMatch> matches) {

		final ICompilationUnit unit = getCompilationUnit(file);
		if (unit == null) return;
		
		MultiTextEdit multiEdit = new MultiTextEdit();
		for (SearchMatch match : matches) {
			multiEdit.addChild(new ReplaceEdit(match.getOffset(), match.getLength(), newName));
		}

		if (!multiEdit.hasChildren())
			return;
		
		
//		TextChangeCompatibility.addTextEdit(changes, TEXT_EDIT_LABEL, multiEdit, TEXTUAL_MATCHES);
		
		TextFileChange change = new TextFileChange(unit.getElementName(), (IFile) unit.getResource());
		change.setTextType("java");
		change.setEdit(multiEdit);
		changes.add(change);
		
		if (willRenameCU(unit)) 
			changes.add(new RenameResourceChange(unit.getPath(), newName + ".java"));
	}
	
	private boolean willRenameCU(final ICompilationUnit unit) {
		if (!(renamingElement instanceof AbstractClassSignature)) 
			return false;
		String name = JavaCore.removeJavaLikeExtension(unit.getElementName());
		if (!((renamingElement.getParent() == null) && name.equals(renamingElement.getName())))
			return false;
		if (!checkNewPathValidity().isOK())
			return false;
		if (!Checks.checkCompilationUnitNewName(unit, newName).isOK())
			return false;
		return true;
	}
	
	protected RefactoringStatus checkIfCuBroken() throws JavaModelException{
		ICompilationUnit cu = getCompilationUnit(renamingElement.getFirstFeatureData().getAbsoluteFilePath());
		if (cu == null)
			return RefactoringStatus.createFatalErrorStatus(RefactoringCoreMessages.Checks_cu_not_created);
		else if (! cu.isStructureKnown())
			return RefactoringStatus.createFatalErrorStatus(RefactoringCoreMessages.Checks_cu_not_parsed);
		return new RefactoringStatus();
	}
	
	protected String getFullFilePathForRenamingElement() {
		return getFullFilePath(renamingElement.getFirstFeatureData().getAbsoluteFilePath());
	}
	
	protected String[] getSourceComplianceLevels() {
		String[] sourceComplianceLevels= new String[] {
				JavaCore.getOption(JavaCore.COMPILER_SOURCE),
				JavaCore.getOption(JavaCore.COMPILER_COMPLIANCE)
		};
		return sourceComplianceLevels;
	}

	private RefactoringStatus checkNewPathValidity() {
		ICompilationUnit unit = getCompilationUnit(renamingElement.getFirstFeatureData().getAbsoluteFilePath());
		IContainer c = unit.getResource().getParent();

		String notRename= RefactoringCoreMessages.RenameTypeRefactoring_will_not_rename;
		IStatus status= c.getWorkspace().validateName(newName, IResource.FILE);
		if (status.getSeverity() == IStatus.ERROR)
			return RefactoringStatus.createWarningStatus(status.getMessage() + ". " + notRename); //$NON-NLS-1$

		status= c.getWorkspace().validatePath(createNewPath(unit, newName), IResource.FILE);
		if (status.getSeverity() == IStatus.ERROR)
			return RefactoringStatus.createWarningStatus(status.getMessage() + ". " + notRename); //$NON-NLS-1$

		return new RefactoringStatus();
	}
	
	private String createNewPath(final ICompilationUnit unit, final String newName) {
		return unit.getResource().getFullPath().removeLastSegments(1).append(newName).toString();
	}
}
