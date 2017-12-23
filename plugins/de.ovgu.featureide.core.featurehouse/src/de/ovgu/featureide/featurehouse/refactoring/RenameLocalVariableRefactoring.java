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
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.matcher.SignatureMatcher;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
@SuppressWarnings("restriction")
public class RenameLocalVariableRefactoring extends RenameRefactoring<FujiLocalVariableSignature> {

	public RenameLocalVariableRefactoring(FujiLocalVariableSignature selection, IFeatureProject featureProject, String file) {
		super(selection, featureProject, file);
	}

	@Override
	public String getName() {
		return RefactoringCoreMessages.RenameTempRefactoring_rename;
	}

	@Override
	protected void checkPreConditions(final SignatureMatcher matcher, final RefactoringStatus refactoringStatus) throws JavaModelException, CoreException {

		super.checkPreConditions(matcher, refactoringStatus);
		if (refactoringStatus.hasFatalError()) return;

		refactoringStatus.merge(checkNameCollision(matcher));
	}

	private RefactoringStatus checkNameCollision(SignatureMatcher matcher) {

		RefactoringStatus status = new RefactoringStatus();

		final AbstractMethodSignature declaringMethod = renamingElement.getDeclaringMethod();
		for (AbstractSignature newMatchedSignature : matcher.getMatchedSignaturesForNewName()) {

			if (!(newMatchedSignature instanceof FujiLocalVariableSignature)) continue;

			for (AFeatureData featureData : newMatchedSignature.getFeatureData()) {

				if ((featureData.getAbsoluteFilePath().equals(file) || declaringMethod.isConstructor())
					&& declaringMethod.equals(((FujiLocalVariableSignature) newMatchedSignature).getDeclaringMethod())) {
					status.addError(
							Messages.format(RefactoringCoreMessages.RefactoringAnalyzeUtil_name_collision, BasicElementLabels.getJavaElementName(newName)));
				}
			}
		}
		return status;
	}

	@Override
	public RefactoringStatus checkNewElementName(String newName) throws CoreException {
		Assert.isNotNull(newName, "new name"); //$NON-NLS-1$
		RefactoringStatus result = Checks.checkName(newName, validateFieldName(newName));

		if (!Checks.startsWithLowerCase(newName)) result.addWarning(RefactoringCoreMessages.RenameTempRefactoring_lowercase);

		return result;
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
