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
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeHierarchy;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.refactoring.base.JavaStatusContext;
import org.eclipse.jdt.internal.corext.refactoring.rename.MethodChecks;
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
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public class RenameMethodRefactoring extends RenameRefactoring<IMethod, AbstractMethodSignature> {

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
	protected void checkPreConditions(final Set<AbstractSignature> newMatchedSignatures, final Set<AbstractSignature> oldMatchedSignatures, final AbstractSignature selectedSignature, final RefactoringStatus refactoringStatus) throws JavaModelException,
			CoreException {
//
//		final IFile file = (IFile) renamingElement.getCompilationUnit().getResource();
//		final IType declaring = renamingElement.getDeclaringType();
//		final String className = renamingElement.getCompilationUnit().getElementName().replaceAll(".java", "");
//
//		final boolean isPrivate = Flags.isPrivate(renamingElement.getFlags());
//		
//		
////		filterMatchedSignatures(selectedSignature, matchedSignatures);
//
//		if (declaring.isInterface() && isSpecialCase()) {
//			refactoringStatus.addError(RefactoringCoreMessages.RenameMethodInInterfaceRefactoring_special_case);
//		} 
//		
//
//		
//		Set<AbstractClassSignature> subClasses = new HashSet<>();
//		addSubClasses2(subClasses, selectedSignature.getParent());
////		filterMatchedSignatures(subClasses, newMatchedSignatures);
//		
//			
////			for (AbstractSignature newMatchedSignature : newMatchedSignatures) {
////				if (!hasSameType(newMatchedSignature)) continue;
////				
////				final FujiMethodSignature methodSignature = (FujiMethodSignature) newMatchedSignature;
////				
////				final FOPFeatureData[] invokedFeatureData = (FOPFeatureData[]) methodSignature.getFeatureData();
////				for (int i = 0; i < invokedFeatureData.length; i++) {
////					final FOPFeatureData fopFeature = invokedFeatureData[i];
////
////					String fileName = fopFeature.getFile().getFullPath().toString();
////					if (fileName.startsWith("/"))
////						fileName = fileName.substring(1);
////					
////					///RefactoringStatusContext context= JavaStatusContext.create(getCompilationUnit(fopFeature.getFile(),);
////					if (hasSameParameters(methodSignature)) {
////						if (fopFeature.getFile().equals(file)) {
////							String message = Messages.format(RefactoringCoreMessages.RenameMethodRefactoring_same_name2, new String[] {
////									BasicElementLabels.getJavaElementName(newName), fileName});
////							refactoringStatus.addError(message);
////
////						} else if (hasSameName(className, methodSignature.getParent().getName())) {
////							String message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines, new String[] { fileName,
////									BasicElementLabels.getJavaElementName(newName) });
////							refactoringStatus.addWarning(message);
////						}
////					} 
//////						else if (hasSameName(className, methodSignature.getParent().getName())) {
//////						String message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines2, new String[] {
//////								BasicElementLabels.getJavaElementName(declaring.getFullyQualifiedName('.')), BasicElementLabels.getJavaElementName(newName) });
//////						refactoringStatus.addWarning(message);
//////					}
////			}
////
////			
////		}
//
//		
//		
////		for (AbstractSignature oldMatchedSignature : oldMatchedSignatures) {
//			if (!hasSameType(selectedSignature)) return;
//			
//			final FujiMethodSignature methodSignature = (FujiMethodSignature) selectedSignature;
//			
////			final FOPFeatureData[] invokedFeatureData = (FOPFeatureData[]) methodSignature.getFeatureData();
////			for (int i = 0; i < invokedFeatureData.length; i++) {
////				final FOPFeatureData fopFeature = invokedFeatureData[i];
////
////				String fileName = fopFeature.getFile().getFullPath().toString();
////				if (fileName.startsWith("/"))
////					fileName = fileName.substring(1);
//				
//				
//				for (AbstractSignature newMatchedSignature : newMatchedSignatures) {
//					if (!hasSameType(newMatchedSignature)) continue;
//					
//					final FujiMethodSignature newMethodSignature = (FujiMethodSignature) newMatchedSignature;
//					
//					if (!hasSameClass(newMethodSignature)) continue;
//					
//					final FOPFeatureData[] newInvokedFeatureData = (FOPFeatureData[]) newMethodSignature.getFeatureData();
//					for (int j = 0; j < newInvokedFeatureData.length; j++) {
//						final FOPFeatureData newFopFeature = newInvokedFeatureData[j];
//
//						String newFileName = newFopFeature.getFile().getFullPath().toString();
//						if (newFileName.startsWith("/"))
//							newFileName = newFileName.substring(1);
//						
//						if (hasSameParameters(newMethodSignature)) {
//							if (file.equals(newFopFeature.getFile())) {
//								String message = Messages.format(RefactoringCoreMessages.RenameMethodRefactoring_same_name2, new String[] {
//										BasicElementLabels.getJavaElementName(newName), newFileName});
//								refactoringStatus.addError(message);
//
//							} else {
//								String message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines, new String[] { newFileName,
//										BasicElementLabels.getJavaElementName(newName) });
//								refactoringStatus.addWarning(message);
//							}
//						}
////							else {
////							String message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines2, new String[] {
////									BasicElementLabels.getJavaElementName(declaring.getFullyQualifiedName('.')), BasicElementLabels.getJavaElementName(newName) });
////							refactoringStatus.addWarning(message);
////						}
//						
//				}
//
//				///RefactoringStatusContext context= JavaStatusContext.create(getCompilationUnit(fopFeature.getFile(),);
//				
////			}
//		}
//				
//				if (!MethodChecks.isVirtual(renamingElement))
//				{	
//				for (AbstractClassSignature subClass : subClasses) {
//					for (AbstractSignature newMatchedSignature : newMatchedSignatures) {
//						if (!hasSameType(newMatchedSignature)) continue;
//						
//						final FujiMethodSignature newMethodSignature = (FujiMethodSignature) newMatchedSignature;
////						if (!newMethodSignature.getParent().equals(subClass)) continue;
//						
//						final FOPFeatureData[] newInvokedFeatureData = (FOPFeatureData[]) newMethodSignature.getFeatureData();
//						for (int j = 0; j < newInvokedFeatureData.length; j++) {
//							final FOPFeatureData newFopFeature = newInvokedFeatureData[j];
//							
//							String newFileName = newFopFeature.getFile().getFullPath().toString();
//							if (newFileName.startsWith("/"))
//								newFileName = newFileName.substring(1);
//							
//							if (hasSameParameters(newMethodSignature) && reduceVisibility(selectedSignature, methodSignature)) {
//								String message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines, new String[] { newFileName,
//										BasicElementLabels.getJavaElementName(newName) });
//								refactoringStatus.addError(message);
//							}
//						}
//						
//					}
//				}
//				}
//		}
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
	
	private boolean reduceVisibility(final AbstractSignature selectedSignature, final FujiMethodSignature methodSignature) {
		if (selectedSignature.isDefault() && (methodSignature.isPrivate()))
			return true;
		if (selectedSignature.isProtected() && (methodSignature.isPrivate() || methodSignature.isDefault()))
			return true;
		if (selectedSignature.isPublic() && (methodSignature.isPrivate() || methodSignature.isDefault() || methodSignature.isProtected()))
			return true;
		return false;
	}

	protected void addSubClasses2(final Set<AbstractClassSignature> result, final AbstractClassSignature classSignature) {
		if (classSignature == null)
			return;

		addSubClassesForNames2(result, classSignature.getSubClassesList());
	}

	protected void addSubClassesForNames2(final Set<AbstractClassSignature> result, final Set<String> names) {
		for (String className : names) {
			if (!classes.containsKey(className))
				continue;

			final AbstractClassSignature classSignature = classes.get(className);
			if (classSignature == null)
				return;

			if (!result.contains(classSignature)) {
				result.add(classSignature);
				addSubClasses2(result, classSignature);
			}
		}
	}

}