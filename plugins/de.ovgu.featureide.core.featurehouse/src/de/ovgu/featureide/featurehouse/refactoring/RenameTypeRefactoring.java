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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaConventions;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.corext.refactoring.Checks;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.viewsupport.BasicElementLabels;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AFeatureData;
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
public class RenameTypeRefactoring extends RenameRefactoring<FujiClassSignature> {

	public RenameTypeRefactoring(FujiClassSignature selection, IFeatureProject featureProject, String file) {
		super(selection, featureProject, file);
	}

	@Override
	public String getName() {
		return RefactoringCoreMessages.RenameTypeProcessor_change_name;
	}

	@Override
	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException, CoreException {
		super.checkPreConditions(matcher, refactoringStatus);
		if (refactoringStatus.hasFatalError()) return;

		refactoringStatus.merge(checkTypesInCompilationUnit(matcher));
	}

	private RefactoringStatus checkTypesInCompilationUnit(final SignatureMatcher matcher) {
		RefactoringStatus result = new RefactoringStatus();

		AbstractSignature selectedSignature = matcher.getSelectedSignature();
		final AFeatureData selectedFeatureData = getFeatureDataForFile(selectedSignature, file);

		if (!(selectedSignature instanceof AbstractClassSignature)) {
			return result;
		}

		AbstractClassSignature classSignature = (AbstractClassSignature) selectedSignature;
		// 1. member types
		for (AbstractClassSignature memberClass : classSignature.getMemberClasses()) {
			if (memberClass.getName().equals(newName)) {
				final FOPFeatureData[] featureData = (FOPFeatureData[]) memberClass.getFeatureData();
				for (int i = 0; i < featureData.length; i++) {
					if (selectedFeatureData.getID() == featureData[i].getID()) {
						result.addError(Messages.format(RefactoringCoreMessages.RenameTypeRefactoring_member_type_exists,
								new String[] { BasicElementLabels.getJavaElementName(newName), getFullFilePath(featureData[i].getAbsoluteFilePath()) }));
					}
				}
			}
		}

		// 2. Methods
		for (AbstractMethodSignature methodSignature : classSignature.getMethods()) {
			if (methodSignature.getName().equals(newName)) {
				final FOPFeatureData[] featureData = (FOPFeatureData[]) methodSignature.getFeatureData();
				for (int i = 0; i < featureData.length; i++) {
					if (selectedFeatureData.getID() == featureData[i].getID()) {
						result.addWarning(Messages.format(RefactoringCoreMessages.Checks_constructor_name, new Object[] {
							BasicElementLabels.getJavaElementName(methodSignature.getName()), getFullFilePath(featureData[i].getAbsoluteFilePath()) }));
					}

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
					if ((parent != null) && (parent.equals(selectedSignature))) continue;

					if ((newMatchedSignature instanceof FujiClassSignature) && newMatchedSignature.isPublic()
						&& packageName.equals(RefactoringUtil.getPackage(newMatchedSignature))) {
						result.addError(Messages.format(RefactoringCoreMessages.RenameTypeRefactoring_name_conflict1,
								new Object[] { newMatchedSignature.getFullName(), selectedSignature.getFullName() }));
					}
				}
			} else if (imported.endsWith("." + newName + ";")) {
				result.addError(Messages.format(RefactoringCoreMessages.RenameTypeRefactoring_imported,
						new Object[] { BasicElementLabels.getJavaElementName(newName), BasicElementLabels
								.getPathLabel(RefactoringUtil.getFile(renamingElement.getFirstFeatureData().getAbsoluteFilePath()).getFullPath(), false) }));
			}
		}

		// 4. types in package
		for (AbstractSignature newMatchedSignature : matcher.getMatchedSignaturesForNewName()) {
			AbstractClassSignature parent = newMatchedSignature.getParent();
			if ((parent != null) && (parent.equals(selectedSignature))) continue;

			if ((newMatchedSignature instanceof FujiClassSignature) && RefactoringUtil.hasSamePackage(selectedSignature, newMatchedSignature)) {
				final FOPFeatureData[] featureData = (FOPFeatureData[]) newMatchedSignature.getFeatureData();
				for (int i = 0; i < featureData.length; i++) {
					if (selectedFeatureData.getID() == featureData[i].getID()) {
						result.addError(Messages.format(RefactoringCoreMessages.RenameTypeRefactoring_exists,
								new String[] { BasicElementLabels.getJavaElementName(newName), ((FujiClassSignature) newMatchedSignature).getPackage() }));
					}
				}
			}
		}

		return result;
	}

	protected AFeatureData getFeatureDataForFile(final AbstractSignature signature, final String file) {
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(file)) return featureData;
		}
		return null;
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
	public RefactoringStatus checkNewElementName(String newName) {
		Assert.isNotNull(newName, "new name"); //$NON-NLS-1$
		RefactoringStatus result = checkTypeName(newName);
		if (renamingElement.getName().equals(newName)) result.addFatalError(RefactoringCoreMessages.RenameTypeRefactoring_choose_another_name);
		return result;
	}

	/**
	 * Checks if the given name is a valid Java type name.
	 *
	 * @param name the java method name.
	 * @param context an {@link IJavaElement} or <code>null</code>
	 * @return a refactoring status containing the error message if the name is not a valid java type name.
	 */
	private RefactoringStatus checkTypeName(String name) {
		if (name.indexOf(".") != -1) //$NON-NLS-1$
			return RefactoringStatus.createFatalErrorStatus(RefactoringCoreMessages.Checks_no_dot);
		else return Checks.checkName(name, validateJavaTypeName(name));
	}

	/**
	 * @param name the name to validate
	 * @param context an {@link IJavaElement} or <code>null</code>
	 * @return validation status in <code>context</code>'s project or in the workspace
	 *
	 * @see JavaConventions#validateJavaTypeName(String, String, String)
	 */
	private IStatus validateJavaTypeName(String name) {
		String[] sourceComplianceLevels = getSourceComplianceLevels();
		return JavaConventions.validateJavaTypeName(name, sourceComplianceLevels[0], sourceComplianceLevels[1]);
	}

}
