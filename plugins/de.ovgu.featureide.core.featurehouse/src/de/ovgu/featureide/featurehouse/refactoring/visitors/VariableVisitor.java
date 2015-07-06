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
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.SuperFieldAccess;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.viewsupport.BasicElementLabels;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringSignature;


/**
 * TODO description
 * 
 * @author steffen
 */
@SuppressWarnings("restriction")
public abstract class VariableVisitor extends AbstractASTVisitor {

	public VariableVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature, final String newName) {
		super(unit, refactoringSignature, newName);
	}

	protected abstract boolean isField();
	
	@Override
	public boolean visit(MethodDeclaration node) {
		return checkMethodBody(node);
	}
	
	@Override
	public boolean visit(Assignment node) {
		if (!(node.getLeftHandSide() instanceof SimpleName)) return true;
		checkIfExpressionCanAddToSearchMatches((SimpleName) node.getLeftHandSide());
		return true;
	}
	
	@Override
	public boolean visit(ArrayAccess node) {
		if (!(node.getArray() instanceof SimpleName)) return true;
		checkIfExpressionCanAddToSearchMatches((SimpleName) node.getArray());
		return false;
	}
	
	@Override
	public boolean visit(SingleVariableDeclaration node) {
		checkIfExpressionCanAddToSearchMatches(node.getName());
		return false;
	}
	
	@Override
	public boolean visit(FieldAccess node) {
		checkIfExpressionCanAddToSearchMatches(node.getName());
		return false;
	}
	
	@Override
	public boolean visit(SuperFieldAccess node) {
		checkIfExpressionCanAddToSearchMatches(node.getName());
		return false;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean visit(FieldDeclaration node) {
		List<VariableDeclarationFragment> fragments = node.fragments();
		for (VariableDeclarationFragment varDeclaration : fragments) {
			checkIfExpressionCanAddToSearchMatches(varDeclaration.getName());
		}
		return false;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean visit(VariableDeclarationStatement node) {
		List<VariableDeclarationFragment> fragments = node.fragments();
		for (VariableDeclarationFragment varDeclaration : fragments) {
			checkIfExpressionCanAddToSearchMatches(varDeclaration.getName());
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
	
	protected boolean checkIfExpressionCanAddToSearchMatches(final SimpleName name){
		final IBinding binding = name.resolveBinding();
		if (!(binding instanceof IVariableBinding)) return false;
		final IVariableBinding varBinding = (IVariableBinding) binding;
		
		if (varBinding.isField() == isField() && hasSameName(refactoringSignature.getDeclaration(), name)) {
			addSearchMatch(getSimpleName(name));
			return true;
		} 
		else if (hasSameName(newName, name.getFullyQualifiedName())){
			if (varBinding.isField())
				addError(Messages.format(RefactoringCoreMessages.RefactoringAnalyzeUtil_name_collision, BasicElementLabels.getJavaElementName(newName)));
			else
				addError(Messages.format(RefactoringCoreMessages.RenameAnalyzeUtil_shadows, BasicElementLabels.getFileName(unit)));
		}
		
		return false;
	}
	
}
