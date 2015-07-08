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
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;

import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.refactoring.SearchMatch;

/**
 * TODO description
 * 
 * @author steffen
 */
public abstract class AbstractASTVisitor extends ASTVisitor implements IASTVisitor {
	protected final RefactoringSignature refactoringSignature;
	private final List<SearchMatch> matches = new ArrayList<>();
	protected boolean checkChildren = false;
	private final Set<String> errors = new HashSet<>();
	protected final String newName;

	public AbstractASTVisitor(final RefactoringSignature refactoringSignature, final String newName) {
		this.refactoringSignature = refactoringSignature;
		this.newName = newName;
	}

	@Override
	public List<SearchMatch> getMatches() {
		return matches;
	}
	
	protected boolean hasSameName(String name, String otherName) {
		return name.equals(otherName);
	}
	
	protected boolean hasSameName(final AbstractSignature signature, final Name name){
		if (name.isQualifiedName())
			return hasSameName(signature, (QualifiedName) name);
		
		return hasSameName(signature, (SimpleName) name);
	}
	
	protected SimpleName getSimpleName(Name nodeName) {
		SimpleName simpleName;
		if (nodeName.isQualifiedName())
			simpleName = (SimpleName) ((QualifiedName) nodeName).getName();
		else
			simpleName = (SimpleName) nodeName;
		return simpleName;
	}

	protected boolean hasSameName(final AbstractSignature signature, final QualifiedName name){
			return hasSameName(signature.getFullName(), getFullQualifiedName(name));
	}
	
	protected boolean hasSameName(final AbstractSignature signature, final SimpleName name){
		return hasSameName(signature.getFullName(), getFullQualifiedName(name));
	}
	
	protected String getFullQualifiedName(final Name name) {
		final IBinding binding = name.resolveBinding();
		if (binding instanceof IVariableBinding){
			final IVariableBinding varBinding = (IVariableBinding) binding;
			final ITypeBinding typeBinding = varBinding.getDeclaringClass();
			return getFullQualifiedName(typeBinding) + "." + getSimpleName(name);
		}
		else if (binding instanceof IMethodBinding){
			final IMethodBinding methodBinding = (IMethodBinding) binding;
			final ITypeBinding typeBinding = methodBinding.getDeclaringClass();
			String qualifiedName = getFullQualifiedName(typeBinding);
			if (!methodBinding.isConstructor()){
				qualifiedName += "." + getSimpleName(name);
			}
			return qualifiedName;
		}
		else if (binding instanceof ITypeBinding){
			final ITypeBinding typeBinding = (ITypeBinding) binding;
			return getFullQualifiedName(typeBinding);
		}
		else 
			return name.getFullyQualifiedName();
	}

	private String getFullQualifiedName(final ITypeBinding typeBinding) {
		String qualifiedName = typeBinding.getQualifiedName();
		if (typeBinding.getPackage().getName().isEmpty()) qualifiedName = "." + qualifiedName;
		return qualifiedName;
	}

	public void startVisit() {
		ASTNode root = RefactoringUtil.parseUnit(refactoringSignature.getRelativePathToFile());
		if (root == null)
			return;
		
		root.accept(this);
	}

	protected void addSearchMatch(SimpleName simpleName) {
		matches.add(new SearchMatch(refactoringSignature.getRelativePathToFile(), simpleName.getStartPosition(), simpleName.getLength()));
	}
	
	protected void addError(String errorMsg) {
		errors.add(errorMsg);
	}
	
	protected boolean checkMethodBody(MethodDeclaration node) {
		for (AbstractSignature aSignature : refactoringSignature.getInvocations()) {
			if (!(aSignature instanceof AbstractMethodSignature))
				continue;

			if (isSameSignature(aSignature, node)) {
				return true;
			}
		}
		return false;
	}


	abstract protected boolean isSameSignature(AbstractSignature sig1, ASTNode sig2);

	public Set<String> getErrors() {
		return errors;
	}
}
