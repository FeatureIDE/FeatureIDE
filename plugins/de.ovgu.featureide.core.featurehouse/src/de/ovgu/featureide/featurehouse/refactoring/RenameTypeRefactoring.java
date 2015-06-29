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

import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.viewsupport.BasicElementLabels;
import org.eclipse.jdt.ui.JavaElementLabels;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public class RenameTypeRefactoring extends RenameRefactoring<IType> {

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
	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException, CoreException {

		refactoringStatus.merge(checkNewElementName(newName));
		if (refactoringStatus.hasFatalError())
			return;
		refactoringStatus.merge(Checks.checkIfCuBroken(renamingElement));
		if (refactoringStatus.hasFatalError())
			return;
		
		refactoringStatus.merge(checkTypesInCompilationUnit(matcher));
	}
	
	
	private RefactoringStatus checkTypesInCompilationUnit(final SignatureMatcher matcher) {
		RefactoringStatus result = new RefactoringStatus();
		
		AbstractSignature selectedSignature = matcher.getSelectedSignature();
		
		if (!(selectedSignature instanceof AbstractClassSignature)) {
			return result;
		}
		
		AbstractClassSignature classSignature = (AbstractClassSignature) selectedSignature;
		// 1. member types
		for (AbstractClassSignature memberClass : classSignature.getMemberClasses()) {
			if (memberClass.getName().equals(newName)) {
				final FOPFeatureData[] featureData = (FOPFeatureData[]) memberClass.getFeatureData();
				for (int i = 0; i < featureData.length; i++) {
					result.addError(
							Messages.format(RefactoringCoreMessages.RenameTypeRefactoring_member_type_exists,
									new String[] { BasicElementLabels.getJavaElementName(newName), getFullFilePath(featureData[i].getAbsoluteFilePath())}));
				}
			}
		}
		
		
		// 2. Methods
		for (AbstractMethodSignature methodSignature : classSignature.getMethods()) {
			if (methodSignature.getName().equals(newName)) {
				final FOPFeatureData[] featureData = (FOPFeatureData[]) methodSignature.getFeatureData();
				for (int i = 0; i < featureData.length; i++) {
					result.addWarning(Messages.format(
						RefactoringCoreMessages.Checks_constructor_name,
						new Object[] { BasicElementLabels.getJavaElementName(methodSignature.getName()), getFullFilePath(featureData[i].getAbsoluteFilePath())}));
			
				}
			} else if (isMainMethod(methodSignature)) {
				result.addWarning(Messages.format(RefactoringCoreMessages.Checks_has_main, selectedSignature.getFullName()));
			}
		}
		
		// 3. imports
		for (String imported : classSignature.getImportList()) {
			if (imported.endsWith(".*;")) {
				String packageName = imported.substring(7, imported.length() - 3);

				for (AbstractSignature newMatchedSignature : matcher.getMatchedSignaturesForNewName()) {
					AbstractClassSignature parent = newMatchedSignature.getParent();
					if ((parent != null) && (parent.equals(selectedSignature)))
						continue;

					if ((newMatchedSignature instanceof FujiClassSignature) && newMatchedSignature.isPublic()
							&& packageName.equals(RefactoringUtil.getPackage(newMatchedSignature))) {
						result.addError(Messages.format(
								RefactoringCoreMessages.RenameTypeRefactoring_name_conflict1,
								new Object[] { newMatchedSignature.getFullName(), selectedSignature.getFullName() }));
					}
				}
			}
			else if (imported.endsWith("." + newName +";")) {
				result.addError(Messages.format(
						RefactoringCoreMessages.RenameTypeRefactoring_imported,
						new Object[] { BasicElementLabels.getJavaElementName(newName),
								BasicElementLabels.getPathLabel(renamingElement.getCompilationUnit().getResource().getFullPath(), false) }));
			}
		}
		
		
		// 4. types in package
		for (AbstractSignature newMatchedSignature : matcher.getMatchedSignaturesForNewName()) {
			AbstractClassSignature parent = newMatchedSignature.getParent();
			if ((parent != null) && (parent.equals(selectedSignature))) continue;
			
			if ((newMatchedSignature instanceof FujiClassSignature) && RefactoringUtil.hasSamePackage(selectedSignature, newMatchedSignature)) {
				final FOPFeatureData[] featureData = (FOPFeatureData[]) newMatchedSignature.getFeatureData();
				for (int i = 0; i < featureData.length; i++) {
					result.addError(Messages.format(
						RefactoringCoreMessages.RenameTypeRefactoring_exists,
						new String[] { BasicElementLabels.getJavaElementName(newName), ((FujiClassSignature) newMatchedSignature).getPackage()}));
				}
			}
		}
		
		return result;
	}

	private boolean isMainMethod(AbstractMethodSignature method) {
		if ("main".equals(method.getName()) && method.getReturnType().equals("void") && method.isPublic() && method.isStatic()) {
			List<String> paramTypes = method.getParameterTypes();
			if (paramTypes.size() == 1) {
				return "String[]".equals(paramTypes.get(0));
			}
		}
		return false;
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