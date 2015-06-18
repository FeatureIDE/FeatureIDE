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
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;


/**
 * TODO description
 * 
 * @author steffen
 */
public class MethodVisitor extends AbstractASTVisitor<AbstractMethodSignature> {

	private boolean checkChildren = false;

	public MethodVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		super(unit, refactoringSignature);
	}

	@Override
	public boolean visit(MethodDeclaration node) {

		if (refactoringSignature.isRenameDeclaration() && isSameSignature((AbstractMethodSignature) refactoringSignature.getDeclaration(), node)) {
			addSearchMatch(node.getName());
			checkChildren = false;
		} else {
			boolean foundInvokedSignature = false;
			for (AbstractSignature aSignature : refactoringSignature.getInvocations()) {
				if (!(aSignature instanceof AbstractMethodSignature))
					continue;

				if (isSameSignature((AbstractMethodSignature) aSignature, node)) {
					foundInvokedSignature = true;
					break;
				}
			}
			checkChildren = foundInvokedSignature;
		}

		return checkChildren;
	}

	@Override
	public boolean visit(MethodInvocation node) {

		if (isSameSignature((AbstractMethodSignature) refactoringSignature.getDeclaration(), node)) {
			addSearchMatch(node.getName());
		}
		return false;
	}

	@Override
	protected <Q extends ASTNode> boolean isSameSignature(AbstractMethodSignature sig1, Q sig2) {

		if (sig2 instanceof MethodDeclaration) {
			MethodDeclaration node = (MethodDeclaration) sig2;
			return (hasSameName(node.getName().getFullyQualifiedName(), sig1.getName()) && hasSameParameters(getNodeParameters(node), sig1.getParameterTypes()));
		} else if (sig2 instanceof MethodInvocation) {
			MethodInvocation node = (MethodInvocation) sig2;
			return (hasSameName(node.getName().getFullyQualifiedName(), sig1.getName()) && hasSameParameters(getNodeParameters(node), sig1.getParameterTypes()));
		}
		return false;
	}

	private boolean hasSameParameters(List<String> parameters, List<String> parameters2) {
		return parameters.equals(parameters2);
	}

	private List<String> getNodeParameters(MethodInvocation node) {
		List<String> parameters = new ArrayList<String>();
		IMethodBinding methodBinding = node.resolveMethodBinding();
		for (ITypeBinding type : methodBinding.getParameterTypes()) {

			parameters.add(type.getErasure().getName());
		}
		return parameters;
	}

	private List<String> getNodeParameters(MethodDeclaration node) {
		List<String> parameters = new ArrayList<String>();
		for (Object parameter : node.parameters()) {
			VariableDeclaration variableDeclaration = (VariableDeclaration) parameter;
			String type = variableDeclaration.getStructuralProperty(SingleVariableDeclaration.TYPE_PROPERTY).toString();
			for (int i = 0; i < variableDeclaration.getExtraDimensions(); i++) {
				type += "[]";
			}
			parameters.add(type);
		}
		return parameters;
	}

}
