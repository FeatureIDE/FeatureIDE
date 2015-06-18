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
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class RenameMethodRefactoring extends RenameRefactoring<IMethod, AbstractMethodSignature> {
	
	
	public RenameMethodRefactoring(IMethod selection, IFeatureProject featureProject) {
		super(selection, featureProject);
	}

	@Override
	public String getName() {
		return "RenameMethod";
	}
	
	private boolean hasSameParameters(final FujiMethodSignature signature) {
		List<String> parameterTypes = signature.getParameterTypes();

		int myParamsLength = renamingElement.getParameterTypes().length;
		String[] simpleNames = new String[myParamsLength];
		for (int i = 0; i < myParamsLength; i++) {
			String erasure = Signature.getTypeErasure(renamingElement.getParameterTypes()[i]);
			simpleNames[i] = Signature.getSimpleName(Signature.toString(erasure));
		}

		return Arrays.equals(simpleNames, parameterTypes.toArray(new String[parameterTypes.size()]));
	}
	
	private boolean hasSameReturnType(final FujiMethodSignature signature) {
		try {
			return signature.getReturnType().equals(Signature.toString(renamingElement.getReturnType()));
		} catch (JavaModelException e) {
			e.printStackTrace();
		}
		return false;
	}

	@Override
	protected boolean checkSignature(AbstractSignature signature) {
		return (signature instanceof FujiMethodSignature) && /*hasSameClass(signature) &&*/ hasSameName(signature.getName(), renamingElement.getElementName())
				&& hasSameParameters((FujiMethodSignature) signature) && hasSameReturnType((FujiMethodSignature) signature);
	}

	@Override
	protected IASTVisitor getASTVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		return new MethodVisitor(unit, refactoringSignature);
	}
	
	@Override
	protected boolean checkPreConditions(RefactoringStatus refactoringStatus) {
		
		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (!(signature instanceof FujiMethodSignature))
				continue;
			final FujiMethodSignature methodSignature = (FujiMethodSignature) signature;

			if (hasSameName(methodSignature.getName(), newName) && hasSameParameters(methodSignature)) {
				final AFeatureData featureData =  methodSignature.getFirstFeatureData();
				if (featureData == null) continue;
				
				String fileName = featureData.getFile().getFullPath().toString();
				if (fileName.startsWith("/"))
					fileName = fileName.substring(1);
				
				refactoringStatus.addError("'" + fileName + "' or a type in its hierarchy defines a methode '"
						+ newName + "' with the same number of parameters and the same parameter type names.");
				return false;
			}

		}
		return true;
	}

	
}