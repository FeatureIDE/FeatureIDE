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

import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringSignature;


/**
 * TODO description
 * 
 * @author steffen
 */
public class FieldVisitor extends AbstractASTVisitor {

	public FieldVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		super(unit, refactoringSignature);
	}

	@Override
	public boolean visit(MethodDeclaration node) {
		return checkMethodBody(node);
	}

	@Override
	public boolean visit(FieldAccess node) {
		if (hasSameName(refactoringSignature.getDeclaration(), node.getName())) {
			addSearchMatch(getSimpleName(node.getName()));
		}
		return false;
	}
	
	@Override
	public boolean visit(SuperFieldAccess node) {
		if (hasSameName(refactoringSignature.getDeclaration(), node.getName())) {
			addSearchMatch(getSimpleName(node.getName()));
		}
		return false;
	}
	
	@Override
	public boolean visit(Assignment node) {
		Expression exp = node.getLeftHandSide();
		if ((exp instanceof SimpleName)  && hasSameName(refactoringSignature.getDeclaration(), (SimpleName) exp)) {
			addSearchMatch(getSimpleName((SimpleName)exp));
			return false;
		}
		return true;
	}
	
//	@Override
//	public boolean visit(VariableDeclarationExpression node) {
//		List<VariableDeclarationFragment> fragments = node.fragments();
//		for (VariableDeclarationFragment varDeclaration : fragments) {
//			if (hasSameName((AbstractFieldSignature) refactoringSignature.getDeclaration(), varDeclaration.getName())) {
//				addSearchMatch(getSimpleName(varDeclaration.getName()));
//			}
//		}
//		return false;
//	}
	
	
//	@Override
//	public boolean visit(ThisExpression node) {
//		Name name = node.getQualifier();
////		for (VariableDeclarationFragment varDeclaration : fragments) {
////			if (hasSameName((AbstractFieldSignature) refactoringSignature.getDeclaration(), varDeclaration.getName())) {
////				addSearchMatch(getSimpleName(varDeclaration.getName()));
////			}
////		}
//		return false;
//	}
//	
//	@SuppressWarnings("unchecked")
//	public boolean visit(VariableDeclarationStatement node) {
//		List<VariableDeclarationFragment> fragments = node.fragments();
//		for (VariableDeclarationFragment varDeclaration : fragments) {
//			if (hasSameName((AbstractFieldSignature) refactoringSignature.getDeclaration(), varDeclaration.getName())) {
//				addSearchMatch(getSimpleName(varDeclaration.getName()));
//			}
//		}
//		return false;
//	}
	
	@SuppressWarnings({ "unchecked" })
	@Override
	public boolean visit(FieldDeclaration node) {
		List<VariableDeclarationFragment> fragments = node.fragments();
		for (VariableDeclarationFragment varDeclaration : fragments) {
			if (hasSameName(refactoringSignature.getDeclaration(), varDeclaration.getName())) {
				addSearchMatch(getSimpleName(varDeclaration.getName()));
			}
		}
		return false;
	}
	
	@Override
	protected boolean isSameSignature(AbstractSignature sig1, ASTNode sig2) {
		
		if (sig2 instanceof MethodDeclaration) {
			return hasSameName(sig1, ((MethodDeclaration) sig2).getName());
		}
		return false;
	}
	
}
