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
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaConventions;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.viewsupport.BasicElementLabels;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.refactoring.matcher.MethodSignatureMatcher;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public class RenameMethodRefactoring extends RenameRefactoring<FujiMethodSignature> {

	public RenameMethodRefactoring(FujiMethodSignature method, IFeatureProject featureProject, String file) {
		super(method, featureProject, file);
	}

	@Override
	public String getName() {
		return RefactoringCoreMessages.RenameMethodProcessor_change_name;
	}

	@Override
	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException, CoreException {

		super.checkPreConditions(matcher, refactoringStatus);
		if (refactoringStatus.hasFatalError()) return;

//		pm.setTaskName(RefactoringCoreMessages.RenameMethodRefactoring_taskName_checkingPreconditions);

//		final AbstractClassSignature declaring = renamingElement.getParent();

//		boolean isInterface =  declaring.getType().equals(ExtendedFujiSignaturesJob.TYPE_INTERFACE);
//		if (isInterface && isSpecialCase()) {
//			refactoringStatus.addError(RefactoringCoreMessages.RenameMethodInInterfaceRefactoring_special_case);
//		} 

//		AbstractMethodSignature topmost = matcher.findDeclaringMethod((FujiMethodSignature)matcher.getSelectedSignature());

		Set<FujiMethodSignature> result = new HashSet<>();
		for (AbstractSignature matchedSignature : matcher.getMatchedSignatures()) {

			if (!(matchedSignature instanceof FujiMethodSignature)) continue;

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
				if (!(newMatchedSignature instanceof FujiMethodSignature)) continue;

				final FujiMethodSignature newMethodSignature = (FujiMethodSignature) newMatchedSignature;

				final AbstractClassSignature clazz = newMethodSignature.getParent();
				boolean found = allClasses.contains(clazz);
				if (!found) continue;

				final boolean isSubclass = subclasses.contains(clazz);

				if (isSubclass || matchedSignature.getParent().equals(clazz)) result.add(newMethodSignature);
				else if (reduceVisibility(newMethodSignature, methodSignature)) result.add(newMethodSignature);
			}
		}

		for (FujiMethodSignature methodSignature : result) {
			final FOPFeatureData[] featureData = (FOPFeatureData[]) methodSignature.getFeatureData();
			for (AFeatureData aFeatureData : featureData) {
				final String file = aFeatureData.getAbsoluteFilePath();

				for (AFeatureData renamingFeatureData : renamingElement.getFeatureData()) {
					if (RefactoringUtil.hasSameParameters(methodSignature, renamingElement)) {
						String message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines,
								new String[] { getFullFilePath(file), BasicElementLabels.getJavaElementName(newName) });
						if (file.equals(renamingFeatureData.getAbsoluteFilePath())) refactoringStatus.addError(message);
						else refactoringStatus.addWarning(message);
					} else {
						String message = Messages.format(RefactoringCoreMessages.RenamePrivateMethodRefactoring_hierarchy_defines2,
								new String[] { getFullFilePath(file), BasicElementLabels.getJavaElementName(newName) });
						refactoringStatus.addWarning(message);
					}
				}
			}
		}
	}

//	private boolean isSpecialCase() throws CoreException {
//		String[] noParams= new String[0];
//		String[] specialNames= new String[]{"toString", "toString", "toString", "toString", "equals", //$NON-NLS-5$ //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
//											"equals", "getClass", "getClass", "hashCode", "notify", //$NON-NLS-5$ //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
//											"notifyAll", "wait", "wait", "wait"}; //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
//		String[][] specialParamTypes= new String[][]{noParams, noParams, noParams, noParams,
//													 {"QObject;"}, {"Qjava.lang.Object;"}, noParams, noParams, //$NON-NLS-2$ //$NON-NLS-1$
//													 noParams, noParams, noParams, {Signature.SIG_LONG, Signature.SIG_INT},
//													 {Signature.SIG_LONG}, noParams};
//		String[] specialReturnTypes= new String[]{"QString;", "QString;", "Qjava.lang.String;", "Qjava.lang.String;", //$NON-NLS-4$ //$NON-NLS-3$ //$NON-NLS-2$ //$NON-NLS-1$
//												   Signature.SIG_BOOLEAN, Signature.SIG_BOOLEAN, "QClass;", "Qjava.lang.Class;", //$NON-NLS-2$ //$NON-NLS-1$
//												   Signature.SIG_INT, Signature.SIG_VOID, Signature.SIG_VOID, Signature.SIG_VOID,
//												   Signature.SIG_VOID, Signature.SIG_VOID};
//		Assert.isTrue((specialNames.length == specialParamTypes.length) && (specialParamTypes.length == specialReturnTypes.length));
//		for (int i= 0; i < specialNames.length; i++){
//			if (specialNames[i].equals(newName)
//				&& Checks.compareParamTypes(renamingElement.getParameterTypes(), specialParamTypes[i])
//				&& !specialReturnTypes[i].equals(renamingElement.getReturnType())){
//					return true;
//			}
//		}
//		return false;
//	}
//	
//	public static boolean compareParamTypes(String[] paramTypes1, String[] paramTypes2) {
//		if (paramTypes1.length == paramTypes2.length) {
//			int i= 0;
//			while (i < paramTypes1.length) {
//				String t1= Signature.getSimpleName(Signature.toString(paramTypes1[i]));
//				String t2= Signature.getSimpleName(Signature.toString(paramTypes2[i]));
//				if (!t1.equals(t2)) {
//					return false;
//				}
//				i++;
//			}
//			return true;
//		}
//		return false;
//	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm) throws CoreException, OperationCanceledException {
		if (renamingElement == null) {
			String message = Messages.format(RefactoringCoreMessages.RenameMethodRefactoring_deleted, getFullFilePathForRenamingElement());
			return RefactoringStatus.createFatalErrorStatus(message);
		}
		return super.checkInitialConditions(pm);
	}

	// RenameMethodProcessor
	@Override
	public RefactoringStatus checkNewElementName(String newName) {
		Assert.isNotNull(newName, "new name");

		RefactoringStatus status = Checks.checkName(newName, validateMethodName(newName));
		if (status.isOK() && !Checks.startsWithLowerCase(newName))
			status = RefactoringStatus.createWarningStatus(Messages.format(RefactoringCoreMessages.Checks_method_names_lowercase2,
					new String[] { BasicElementLabels.getJavaElementName(newName), ""/* getDeclaringTypeLabel() */ }));

		if (renamingElement.getName().equals(newName)) status.addFatalError(RefactoringCoreMessages.RenameMethodRefactoring_same_name);
		return status;
	}

	/**
	 * @param name the name to validate
	 * @param context an {@link IJavaElement} or <code>null</code>
	 * @return validation status in <code>context</code>'s project or in the workspace
	 *
	 * @see JavaConventions#validateMethodName(String, String, String)
	 */
	public IStatus validateMethodName(String name) {
		String[] sourceComplianceLevels = new String[] { JavaCore.getOption(JavaCore.COMPILER_SOURCE), JavaCore.getOption(JavaCore.COMPILER_COMPLIANCE) };
		return JavaConventions.validateMethodName(name, sourceComplianceLevels[0], sourceComplianceLevels[1]);
	}

//	private String getDeclaringTypeLabel() {
//		return JavaElementLabels.getElementLabel(renamingElement.getDeclaringType(), JavaElementLabels.ALL_DEFAULT);
//	}

	private boolean reduceVisibility(final FujiMethodSignature selectedSignature, final FujiMethodSignature methodSignature) {
		if (selectedSignature.isDefault() && (methodSignature.isPrivate())) return true;
		if (selectedSignature.isProtected() && (methodSignature.isPrivate() || methodSignature.isDefault())) return true;
		if (selectedSignature.isPublic() && (methodSignature.isPrivate() || methodSignature.isDefault() || methodSignature.isProtected())) return true;
		return false;
	}
}
