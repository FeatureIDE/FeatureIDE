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
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public class RenameFieldRefactoring extends RenameRefactoring<FujiFieldSignature> {

	public RenameFieldRefactoring(FujiFieldSignature selection, IFeatureProject featureProject, String file) {
		super(selection, featureProject, file);
	}

	@Override
	public String getName() {
		return RefactoringCoreMessages.RenameFieldRefactoring_name;
	}

	@Override
	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException, CoreException {

		super.checkPreConditions(matcher, refactoringStatus);
		if (refactoringStatus.hasFatalError()) return;

		AbstractClassSignature parent = matcher.getSelectedSignature().getParent();
		if (existField(parent) != null) {
			refactoringStatus.addError(RefactoringCoreMessages.RenameFieldRefactoring_field_already_defined);
			return;
		}

		refactoringStatus.merge(checkEnclosingHierarchy(parent));
		refactoringStatus.merge(checkNestedHierarchy(parent));
	}

	private RefactoringStatus checkNestedHierarchy(AbstractClassSignature parent) throws CoreException {
		RefactoringStatus result = new RefactoringStatus();
		for (AbstractClassSignature memberClass : parent.getMemberClasses()) {
			final AbstractFieldSignature field = existField(memberClass);
			if (field != null) {
				String msg = Messages.format(RefactoringCoreMessages.RenameFieldRefactoring_hiding,
						new String[] { BasicElementLabels.getJavaElementName(renamingElement.getName()), BasicElementLabels.getJavaElementName(newName),
							BasicElementLabels.getJavaElementName(field.getName()) });
				result.addWarning(msg);
			}
			result.merge(checkNestedHierarchy(memberClass));
		}
		return result;
	}

	private RefactoringStatus checkEnclosingHierarchy(AbstractClassSignature parent) {
		if (parent == null) return null;
		RefactoringStatus result = new RefactoringStatus();
		while (parent != null) {
			final AbstractFieldSignature field = existField(parent);
			if (field != null) {
				String msg =
					Messages.format(RefactoringCoreMessages.RenameFieldRefactoring_hiding2, new String[] { BasicElementLabels.getJavaElementName(newName),
						BasicElementLabels.getJavaElementName(parent.getFullName()), BasicElementLabels.getJavaElementName(field.getName()) });
				result.addWarning(msg);
			}
			parent = parent.getParent();
		}
		return result;
	}

	@Override
	public RefactoringStatus checkNewElementName(String newName) throws CoreException {
		Assert.isNotNull(newName, "new name"); //$NON-NLS-1$
		RefactoringStatus result = Checks.checkName(newName, validateFieldName(newName));

		if (isInstanceField() && (!Checks.startsWithLowerCase(newName)))
			result.addWarning(Messages.format(RefactoringCoreMessages.RenameFieldRefactoring_should_start_lowercase2,
					new String[] { BasicElementLabels.getJavaElementName(newName), renamingElement.getParent().getName() }));

		if (renamingElement.getName().equals(newName)) result.addError(Messages.format(RefactoringCoreMessages.RenameFieldRefactoring_another_name2,
				new String[] { BasicElementLabels.getJavaElementName(newName), renamingElement.getParent().getName() }));

		return result;
	}

	private AbstractFieldSignature existField(final AbstractClassSignature parent) {
		for (AbstractFieldSignature field : parent.getFields()) {
			if (field.getName().equals(newName)) {
				final FOPFeatureData[] featureData = (FOPFeatureData[]) field.getFeatureData();
				for (int i = 0; i < featureData.length; i++) {
					if (featureData[i].getAbsoluteFilePath().equals(file)) return field;
				}
			}
		}
		return null;
	}

	private boolean isInstanceField() throws CoreException {
		AbstractClassSignature parent = renamingElement.getParent();

		if ((parent != null) && (parent.isInterface())) return false;
		else return !renamingElement.isStatic();
	}

	/**
	 * @param name the name to validate
	 * @param context an {@link IJavaElement} or <code>null</code>
	 * @return validation status in <code>context</code>'s project or in the workspace
	 *
	 * @see JavaConventions#validateFieldName(String, String, String)
	 */
	private IStatus validateFieldName(String name) {
		String[] sourceComplianceLevels = getSourceComplianceLevels();
		return JavaConventions.validateFieldName(name, sourceComplianceLevels[0], sourceComplianceLevels[1]);
	}

}
