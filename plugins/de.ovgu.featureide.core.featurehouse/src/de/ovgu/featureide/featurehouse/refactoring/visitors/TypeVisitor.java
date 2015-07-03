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

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.TypeLiteral;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringSignature;


/**
 * TODO description
 * 
 * @author steffen
 */
public class TypeVisitor extends AbstractASTVisitor {

	public TypeVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		super(unit, refactoringSignature);
	}

	@Override
	public boolean visit(TypeDeclaration node) {
		if (hasSameName(refactoringSignature.getDeclaration(), node.getName())) {
			addSearchMatch(getSimpleName(node.getName()));
		} 
		
		return true;
	}
	
	@Override
	public boolean visit(SimpleType node) {
		if (hasSameName(refactoringSignature.getDeclaration(), node.getName())) {
			addSearchMatch(getSimpleName(node.getName()));
		} 
		return false;
	}
	
//	@Override
//	public boolean visit(ClassInstanceCreation node) {
//		Type type = node.getType();
//		if (type instanceof SimpleType) {
//			SimpleType simpleType = (SimpleType) type;
//			if (hasSameName(refactoringSignature.getDeclaration(), simpleType.getName())) {
//				addSearchMatch(getSimpleName(simpleType.getName()));
//			}
//		}
//		return false;
//	}

	@Override
	public boolean visit(MethodDeclaration node) {
		if (hasSameName(refactoringSignature.getDeclaration(), node.getName()) && node.isConstructor()) {
			addSearchMatch(getSimpleName(node.getName()));
			checkChildren = false;
		} else {
			checkChildren = checkMethodBody(node);
		}

		return checkChildren;
	}

	@Override
	public boolean visit(ImportDeclaration node) {
		
		if (hasSameName(refactoringSignature.getDeclaration(), node.getName())) {
			addSearchMatch(getSimpleName(node.getName()));
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
