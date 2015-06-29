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

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.refactoring.base.JavaStatusContext;
import org.eclipse.jdt.internal.corext.refactoring.rename.MethodChecks;
import org.eclipse.jdt.internal.corext.util.JavaConventionsUtil;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.viewsupport.BasicElementLabels;
import org.eclipse.jdt.ui.JavaElementLabels;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.matcher.MethodSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public class RenameMethodRefactoring extends RenameRefactoring<IMethod> {

	public RenameMethodRefactoring(IMethod selection, IFeatureProject featureProject) {
		super(selection, featureProject);
	}

	@Override
	public String getName() {
		return RefactoringCoreMessages.RenameMethodProcessor_change_name;
	}



	@Override
	protected IASTVisitor getASTVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		return new MethodVisitor(unit, refactoringSignature);
	}

	@Override
	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException,
			CoreException {
		
		if (!Checks.isAvailable(renamingElement)) {
			refactoringStatus.addFatalError(RefactoringCoreMessages.RenameMethodProcessor_is_binary, JavaStatusContext.create(renamingElement));
			return;
		}
		refactoringStatus.merge(Checks.checkIfCuBroken(renamingElement));
		if (refactoringStatus.hasFatalError())
			return;
//		pm.setTaskName(RefactoringCoreMessages.RenameMethodRefactoring_taskName_checkingPreconditions);
		refactoringStatus.merge(checkNewElementName(newName));
		if (refactoringStatus.hasFatalError())
			return;

		final IType declaring = renamingElement.getDeclaringType();

		if (declaring.isInterface() && isSpecialCase()) {
			refactoringStatus.addError(RefactoringCoreMessages.RenameMethodInInterfaceRefactoring_special_case);
		} 

//		AbstractMethodSignature topmost = matcher.findDeclaringMethod((FujiMethodSignature)matcher.getSelectedSignature());
		
		Set<FujiMethodSignature> result = new HashSet<>();
		for (AbstractSignature matchedSignature : matcher.getMatchedSignatures()) {
			
			if (!(matchedSignature instanceof FujiMethodSignature))
				continue;

			final FujiMethodSignature methodSignature = (FujiMethodSignature) matchedSignature;
			
			Set<AbstractClassSignature> superclasses = new HashSet<>();
			Set<AbstractClassSignature> subclasses = new HashSet<>();
			((MethodSignatureMatcher) matcher).addSubClasses(subclasses, matchedSignature.getParent());
			((MethodSignatureMatcher) matcher).addSuperClasses(superclasses, matchedSignature.getParent());
			
			Set<AbstractClassSignature> allClasses = new HashSet<>();
			allClasses.addAll(subclasses);
			allClasses.add(matchedSignature.getParent());
			allClasses.addAll(superclasses);
			
			for (AbstractSignature newMatchedSignature : matcher.getMatchedSignaturesForNewName()) {
				if (!(newMatchedSignature instanceof FujiMethodSignature))
					continue;

				final FujiMethodSignature newMethodSignature = (FujiMethodSignature) newMatchedSignature;
				
				final AbstractClassSignature clazz = newMethodSignature.getParent();
				boolean found = allClasses.contains(clazz);
				if (!found)
					continue;
				
				final boolean isSubclass = subclasses.contains(clazz);
				
				if (isSubclass || matchedSignature.getParent().equals(clazz))
					result.add(newMethodSignature);
				else if (reduceVisibility(newMethodSignature, methodSignature))
					result.add(newMethodSignature);
			}
		}
		
		for (FujiMethodSignature methodSignature : result) {
			if (RefactoringUtil.hasSameParameters(methodSignature, renamingElement)) {
				String message;
				if (MethodChecks.isVirtual(renamingElement)) {
					message = Messages.format(RefactoringCoreMessages.RenameVirtualMethodRefactoring_hierarchy_declares1,
							new String[] { BasicElementLabels.getJavaElementName(methodSignature.getName()) });
				} else {
					message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines, 
							new String[] { methodSignature.getParent().getFullName(), BasicElementLabels.getJavaElementName(newName) });
				}
				refactoringStatus.addError(message);
			} else {
				String message;
				if (MethodChecks.isVirtual(renamingElement)) {
					message = Messages.format(RefactoringCoreMessages.RenameVirtualMethodRefactoring_hierarchy_declares2,
							new String[] { BasicElementLabels.getJavaElementName(methodSignature.getName()) });
				} else {
					message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines2, 
							new String[] { methodSignature.getParent().getFullName(), BasicElementLabels.getJavaElementName(newName) });
				}
				refactoringStatus.addWarning(message);
			}
		}
	}
	
	private boolean isSpecialCase() throws CoreException {
		String[] noParams= new String[0];
		String[] specialNames= new String[]{"toString", "toString", "toString", "toString", "equals", //$NON-NLS-5$ //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
											"equals", "getClass", "getClass", "hashCode", "notify", //$NON-NLS-5$ //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
											"notifyAll", "wait", "wait", "wait"}; //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
		String[][] specialParamTypes= new String[][]{noParams, noParams, noParams, noParams,
													 {"QObject;"}, {"Qjava.lang.Object;"}, noParams, noParams, //$NON-NLS-2$ //$NON-NLS-1$
													 noParams, noParams, noParams, {Signature.SIG_LONG, Signature.SIG_INT},
													 {Signature.SIG_LONG}, noParams};
		String[] specialReturnTypes= new String[]{"QString;", "QString;", "Qjava.lang.String;", "Qjava.lang.String;", //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
												   Signature.SIG_BOOLEAN, Signature.SIG_BOOLEAN, "QClass;", "Qjava.lang.Class;", //$NON-NLS-2$ //$NON-NLS-1$
												   Signature.SIG_INT, Signature.SIG_VOID, Signature.SIG_VOID, Signature.SIG_VOID,
												   Signature.SIG_VOID, Signature.SIG_VOID};
		Assert.isTrue((specialNames.length == specialParamTypes.length) && (specialParamTypes.length == specialReturnTypes.length));
		for (int i= 0; i < specialNames.length; i++){
			if (specialNames[i].equals(newName)
				&& Checks.compareParamTypes(renamingElement.getParameterTypes(), specialParamTypes[i])
				&& !specialReturnTypes[i].equals(renamingElement.getReturnType())){
					return true;
			}
		}
		return false;
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		if (!renamingElement.exists()) {
			String message = Messages.format(RefactoringCoreMessages.RenameMethodRefactoring_deleted,
					BasicElementLabels.getFileName(renamingElement.getCompilationUnit()));
			return RefactoringStatus.createFatalErrorStatus(message);
		}

		RefactoringStatus result = Checks.checkAvailability(renamingElement);
		if (result.hasFatalError())
			return result;
		result.merge(Checks.checkIfCuBroken(renamingElement));
		return result;
	}

	//RenameMethodProcessor
	@Override
	public RefactoringStatus checkNewElementName(String newName) {
		Assert.isNotNull(newName, "new name"); 

		RefactoringStatus status = Checks.checkName(newName, JavaConventionsUtil.validateMethodName(newName, renamingElement));
		if (status.isOK() && !Checks.startsWithLowerCase(newName))
			status = RefactoringStatus.createWarningStatus(Messages.format(RefactoringCoreMessages.Checks_method_names_lowercase2, new String[] {
					BasicElementLabels.getJavaElementName(newName), getDeclaringTypeLabel() }));

		if (Checks.isAlreadyNamed(renamingElement, newName))
			status.addFatalError(RefactoringCoreMessages.RenameMethodRefactoring_same_name, JavaStatusContext.create(renamingElement));
		return status;
	}

	private String getDeclaringTypeLabel() {
		return JavaElementLabels.getElementLabel(renamingElement.getDeclaringType(), JavaElementLabels.ALL_DEFAULT);
	}
	
	private boolean reduceVisibility(final FujiMethodSignature selectedSignature, final FujiMethodSignature methodSignature) {
		if (selectedSignature.isDefault() && (methodSignature.isPrivate()))
			return true;
		if (selectedSignature.isProtected() && (methodSignature.isPrivate() || methodSignature.isDefault()))
			return true;
		if (selectedSignature.isPublic() && (methodSignature.isPrivate() || methodSignature.isDefault() || methodSignature.isProtected()))
			return true;
		return false;
	}
}