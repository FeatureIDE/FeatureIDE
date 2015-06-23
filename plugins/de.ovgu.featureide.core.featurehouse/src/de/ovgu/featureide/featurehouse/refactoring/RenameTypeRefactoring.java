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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeHierarchy;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.refactoring.base.JavaStatusContext;
import org.eclipse.jdt.internal.corext.refactoring.rename.RenameTypeProcessor;
import org.eclipse.jdt.internal.corext.util.JavaConventionsUtil;
import org.eclipse.jdt.internal.corext.util.JdtFlags;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.viewsupport.BasicElementLabels;
import org.eclipse.jdt.ui.JavaElementLabels;
import org.eclipse.jdt.ui.refactoring.RenameSupport;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.RefactoringStatusContext;
import org.eclipse.ltk.core.refactoring.participants.RenameProcessor;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public class RenameTypeRefactoring extends RenameRefactoring<IType, AbstractClassSignature> {

	public RenameTypeRefactoring(IType selection, IFeatureProject featureProject) {
		super(selection, featureProject);
	}

	@Override
	public String getName() {
		return RefactoringCoreMessages.RenameTypeProcessor_change_name;
	}

	@Override
	protected IASTVisitor getASTVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		return new TypeVisitor(unit, refactoringSignature);
	}

	@Override
	protected void checkPreConditions(final Set<AbstractSignature> newMatchedSignatures, final Set<AbstractSignature> oldMatchedSignatures, final AbstractSignature selectedSignature, final RefactoringStatus refactoringStatus) throws JavaModelException,
			CoreException {

	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {

		IType primary= (IType) renamingElement.getPrimaryElement();
		if (primary == null || !primary.exists()) {
			String qualifiedTypeName= JavaElementLabels.getElementLabel(renamingElement, JavaElementLabels.F_FULLY_QUALIFIED);
			String message= Messages.format(RefactoringCoreMessages.RenameTypeRefactoring_does_not_exist, new String[] { BasicElementLabels.getJavaElementName(qualifiedTypeName), BasicElementLabels.getFileName(renamingElement.getCompilationUnit())});
			return RefactoringStatus.createFatalErrorStatus(message);
		}
		return Checks.checkIfCuBroken(renamingElement);
	}

	@Override
	public RefactoringStatus checkNewElementName(String newName) {
		Assert.isNotNull(newName, "new name"); //$NON-NLS-1$
		RefactoringStatus result= Checks.checkTypeName(newName, renamingElement);
		if (Checks.isAlreadyNamed(renamingElement, newName))
			result.addFatalError(RefactoringCoreMessages.RenameTypeRefactoring_choose_another_name);
		return result;
	}

}