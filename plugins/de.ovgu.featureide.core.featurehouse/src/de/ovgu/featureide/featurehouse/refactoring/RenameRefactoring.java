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
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.refactoring.changes.RenameCompilationUnitChange;
import org.eclipse.jdt.internal.corext.refactoring.rename.RenameTypeProcessor;
import org.eclipse.jdt.internal.corext.util.JavaModelUtil;
import org.eclipse.jdt.ui.refactoring.RenameSupport;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.Refactoring;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.resource.RenameResourceChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.featurehouse.refactoring.matcher.MethodSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.TypeSignatureMatcher;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public abstract class RenameRefactoring<T extends IMember, Q extends AbstractSignature> extends Refactoring {

	protected final IFeatureProject featureProject;
	protected final T renamingElement;
	protected ProjectSignatures signatures;
	protected String newName;
	private List<Change> changes = new ArrayList<Change>();
	protected Map<String, AbstractClassSignature> classes = new HashMap<>();
	private Map<ICompilationUnit, List<SearchMatch>> nodes = new HashMap<>();

	public RenameRefactoring(T selection, IFeatureProject featureProject) {
		this.renamingElement = selection;
		this.featureProject = featureProject;
		this.newName = renamingElement.getElementName();
	}

	public void setNewName(String newName) {
		this.newName = newName;
	}

	public String getNewName() {
		return this.newName;
	}

	protected abstract IASTVisitor getASTVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature);

	protected abstract void checkPreConditions(final Set<AbstractSignature> newMatchedSignatures, final Set<AbstractSignature> oldMatchedSignatures, final AbstractSignature selectedSignature, final RefactoringStatus status) throws JavaModelException, CoreException;
	
	protected abstract RefactoringStatus checkNewElementName(String newName);

	@Override
	public final RefactoringStatus checkFinalConditions(final IProgressMonitor pm) throws CoreException, OperationCanceledException {
		final RefactoringStatus refactoringStatus = new RefactoringStatus();
		try {
			pm.beginTask("Checking preconditions...", 2);

			ExtendedFujiSignaturesJob efsj = new ExtendedFujiSignaturesJob(featureProject);
			efsj.schedule();
			efsj.join();

			// pruefen, ob neues Element schon existiert

			signatures = featureProject.getFSTModel().getProjectSignatures();
			if (signatures == null)
				return refactoringStatus;

			pm.setTaskName(RefactoringCoreMessages.RenameMethodRefactoring_taskName_checkingPreconditions);
//			if (!)
//				return refactoringStatus;
			
			SignatureMatcher matcher = null;
			if (renamingElement instanceof IMethod)
				matcher = new MethodSignatureMatcher(signatures, renamingElement, newName);
			else if (renamingElement instanceof IType)
				matcher = new TypeSignatureMatcher(signatures, renamingElement, newName);
			
			if (matcher == null)
				return refactoringStatus;
			
			matcher.findMatchedSignatures();
			
			//checkPreConditions(getNamedMatchedSignatures(newName), matchedSignatures, selectedSignature, refactoringStatus);
			if (refactoringStatus.hasFatalError()) 
				return refactoringStatus;
			
			if (matcher.getSelectedSignature() != null) {

				for (RefactoringSignature refactoringSignature : createRefactoringSignatures(matcher)) {
					search(refactoringSignature);
				}

				for (Entry<ICompilationUnit, List<SearchMatch>> searchMatches : nodes.entrySet()) {
					rewriteAST(searchMatches.getKey(), searchMatches.getValue());
				}
			}

		} catch (InterruptedException e) {
			e.printStackTrace();
		} finally {
			pm.done();
		}
		return refactoringStatus;
	}

//	private Set<RefactoringSignature> getInvolvedSignatures(final AbstractSignature selectedSignature, final Set<AbstractSignature> matchedSignatures) {
//		
////		filterMatchedSignatures(selectedSignature, matchedSignatures);
//		
//		Set<RefactoringSignature> refactoringSignatures = createRefactoringSignatures(matchedSignatures);
//
//		handleInvokedSignatureOfMatchedSignature(refactoringSignatures, selectedSignature);
//		final FOPFeatureData[] featureData = (FOPFeatureData[]) selectedSignature.getFeatureData();
//		for (int j = 0; j < featureData.length; j++) {
//			final FOPFeatureData fopFeature = featureData[j];
//
//			addToRefactoringSignatures(refactoringSignatures, selectedSignature, fopFeature.getFile());
//		}
//
//		return refactoringSignatures;
//	}

	private Set<RefactoringSignature> createRefactoringSignatures(final SignatureMatcher matcher) {
		Set<RefactoringSignature> result = new HashSet<>();

		for (AbstractSignature matchedSignature : matcher.getMatchedSignatures()) {

			handleInvokedSignatureOfMatchedSignature(result, matchedSignature);

			final FOPFeatureData[] featureData = (FOPFeatureData[]) matchedSignature.getFeatureData();
			for (int j = 0; j < featureData.length; j++) {
				final FOPFeatureData fopFeature = featureData[j];

				addToRefactoringSignatures(result, matcher.getSelectedSignature(), fopFeature.getFile());
			}
		}

		return result;
	}

	private void addToRefactoringSignatures(Set<RefactoringSignature> result, AbstractSignature matchedSignature, final IFile file) {
		RefactoringSignature signature = getRefactoringSignature(result, file);
		if (signature == null) {
			signature = new RefactoringSignature(file, matchedSignature);
			result.add(signature);
		} else if (signature.getDeclaration() == null) {
			signature.setDeclaration(matchedSignature);
		}
		signature.setRenameDeclaration(true);
	}

	private void handleInvokedSignatureOfMatchedSignature(Set<RefactoringSignature> result, AbstractSignature matchedSignature) {

		for (FOPFeatureData featureData : (FOPFeatureData[]) matchedSignature.getFeatureData()) {

			for (AbstractSignature invokedSignature : featureData.getInvokedSignatures()) {
				final FOPFeatureData[] invokedFeatureData = (FOPFeatureData[]) invokedSignature.getFeatureData();
				for (int i = 0; i < invokedFeatureData.length; i++) {
					final FOPFeatureData fopFeature = invokedFeatureData[i];
					final IFile file = fopFeature.getFile();

					RefactoringSignature signature = getRefactoringSignature(result, file);
					if (signature == null) {

						signature = new RefactoringSignature(file, matchedSignature);
						result.add(signature);
					}

					signature.addInvocation(invokedSignature);
				}
			}
		}
	}

	private RefactoringSignature getRefactoringSignature(final Set<RefactoringSignature> result, final IFile file) {
		for (RefactoringSignature refactoringSignature : result) {
			if (refactoringSignature.getFile().equals(file))
				return refactoringSignature;
		}
		return null;
	}

	private void search(final RefactoringSignature refactoringSignatures) {

		final ICompilationUnit unit = getCompilationUnit(refactoringSignatures.getFile());
		if (unit == null)
			return;

		IASTVisitor visitor = getASTVisitor(unit, refactoringSignatures);
		visitor.startVisit();

		nodes.put(unit, visitor.getMatches());
	}
	
	protected ICompilationUnit getCompilationUnit(final IFile file)
	{
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

	private void rewriteAST(ICompilationUnit unit, List<SearchMatch> matches) {

		MultiTextEdit multiEdit = new MultiTextEdit();
		for (SearchMatch match : matches) {
			multiEdit.addChild(new ReplaceEdit(match.getOffset(), match.getLength(), newName));
		}

		if (!multiEdit.hasChildren())
			return;
		
		TextFileChange change = new TextFileChange(unit.getElementName(), (IFile) unit.getResource());
		change.setTextType("java");
		change.setEdit(multiEdit);
		changes.add(change);
		
		if (willRenameCU(unit)) 
			changes.add(new RenameResourceChange(unit.getPath(), newName + ".java"));
	}
	
	private boolean willRenameCU(final ICompilationUnit unit) {
		if (!(renamingElement instanceof IType)) 
			return false;
		String name = JavaCore.removeJavaLikeExtension(unit.getElementName());
		if (! (Checks.isTopLevel((IType)renamingElement) && name.equals(renamingElement.getElementName())))
			return false;
		if (! checkNewPathValidity().isOK())
			return false;
		if (! Checks.checkCompilationUnitNewName(unit, newName).isOK())
			return false;
		return true;
	}

	private RefactoringStatus checkNewPathValidity() {
		IContainer c = renamingElement.getCompilationUnit().getResource().getParent();

		String notRename= RefactoringCoreMessages.RenameTypeRefactoring_will_not_rename;
		IStatus status= c.getWorkspace().validateName(newName, IResource.FILE);
		if (status.getSeverity() == IStatus.ERROR)
			return RefactoringStatus.createWarningStatus(status.getMessage() + ". " + notRename); //$NON-NLS-1$

		status= c.getWorkspace().validatePath(createNewPath(newName), IResource.FILE);
		if (status.getSeverity() == IStatus.ERROR)
			return RefactoringStatus.createWarningStatus(status.getMessage() + ". " + notRename); //$NON-NLS-1$

		return new RefactoringStatus();
	}
	
	private String createNewPath(String newName) {
		return renamingElement.getCompilationUnit().getResource().getFullPath().removeLastSegments(1).append(newName).toString();
	}
}
