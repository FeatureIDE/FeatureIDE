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
package de.ovgu.featureide.featurehouse.refactoring.visitors;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.SuperMethodInvocation;
import org.eclipse.jdt.core.dom.VariableDeclaration;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;


/**
 * TODO description
 * 
 * @author steffen
 */
public class MethodVisitor extends AbstractASTVisitor {

	public MethodVisitor(final RefactoringSignature refactoringSignature, final String newName) {
		super(refactoringSignature, newName);
	}

	@Override
	public boolean visit(MethodDeclaration node) {
		if (isSameSignature(refactoringSignature.getDeclaration(), node)) {
			addSearchMatch(getSimpleName(node.getName()));
		}

		return checkMethodBody(node);
	}

	@Override
	public boolean visit(MethodInvocation node) {
		Set<AbstractSignature> invokedSignatures = refactoringSignature.getInvocations().get(methodDeclaration);
		for (AbstractSignature invokedSignature : invokedSignatures) {
			if (isSameSignature(invokedSignature, node)) {
				addSearchMatch(getSimpleName(node.getName()));
				return false;
			}
		}
		
		return false;
	}
	
	@Override
	public boolean visit(SuperMethodInvocation node) {
		Set<AbstractSignature> invokedSignatures = refactoringSignature.getInvocations().get(methodDeclaration);
		for (AbstractSignature invokedSignature : invokedSignatures) {
			if (isSameSignature(invokedSignature, node)) {
				addSearchMatch(getSimpleName(node.getName()));
				return false;
			}
		}
		return false;
	}

	@Override
	protected boolean isSameSignature(AbstractSignature sig1, ASTNode sig2) {

		if (!(sig1 instanceof FujiMethodSignature)) return false;
		final FujiMethodSignature method = (FujiMethodSignature) sig1;
		
		if (sig2 instanceof MethodDeclaration) {
			final MethodDeclaration node = (MethodDeclaration) sig2;
			return (hasSameName(sig1, node.getName()) && hasSameParameters(getNodeParameters(node), method.getParameterTypes()));
		} else if (sig2 instanceof MethodInvocation) {
			final MethodInvocation node = (MethodInvocation) sig2;
			return (hasSameName(sig1, node.getName()) && hasSameParameters(getNodeParameters(node), method.getParameterTypes()));
		} else if (sig2 instanceof SuperMethodInvocation) {
			final SuperMethodInvocation node = (SuperMethodInvocation) sig2;
			return (hasSameName(sig1, node.getName()) && hasSameParameters(getNodeParameters(node), method.getParameterTypes()));
		}
		return false;
	}

	private boolean hasSameParameters(List<String> parameters, List<String> parameters2) {
		return parameters.equals(parameters2);
	}

	private List<String> getNodeParameters(MethodInvocation node) {
		return getNodeParameters(node.arguments(), node.resolveMethodBinding());
	}
	
	private List<String> getNodeParameters(SuperMethodInvocation node) {
		return getNodeParameters(node.arguments(), node.resolveMethodBinding());
	}

	private List<String> getNodeParameters(List arguments, IMethodBinding methodBinding) {
		final List<String> parameters = new ArrayList<>();
		if (methodBinding == null) {
			for (Iterator it = arguments.iterator(); it.hasNext();) {
				Expression e = (Expression) it.next();
				parameters.add(e.resolveTypeBinding().getErasure().getName());
			}
		} else {
			for (ITypeBinding type : methodBinding.getParameterTypes()) {
				parameters.add(type.getErasure().getName());
			}
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
