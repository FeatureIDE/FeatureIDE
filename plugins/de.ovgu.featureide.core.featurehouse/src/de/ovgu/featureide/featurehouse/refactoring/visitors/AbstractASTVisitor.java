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
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
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
	private List<SearchMatch> matches = new ArrayList<>();
	private final ICompilationUnit unit;
	protected boolean checkChildren = false;

	public AbstractASTVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		this.unit = unit;
		this.refactoringSignature = refactoringSignature;
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
			return hasSameName(signature.getFullName(), name.getFullyQualifiedName());
	}
	
	protected boolean hasSameName(final AbstractSignature signature, final SimpleName name){
		return hasSameName(signature.getName(), name.getFullyQualifiedName());
	}
	
//	private String getFullQualifiedName(final Name name) {
//		IBinding binding = name.resolveBinding();
//		if (binding instanceof IVariableBinding){
//			final IVariableBinding varBinding = (IVariableBinding) binding;
//			final ITypeBinding typeBinding = varBinding.getDeclaringClass();
//			return packageName + typeBinding.getQualifiedName() + "." +getSimpleName(name);
//		}
//		else if (binding instanceof IMethodBinding){
//			final IMethodBinding methodBinding = (IMethodBinding) binding;
//			final ITypeBinding typeBinding = methodBinding.getDeclaringClass();
//			String qualifiedName = packageName + typeBinding.getQualifiedName();
//			if (!methodBinding.isConstructor()){
//				qualifiedName += "." +getSimpleName(name);
//			}
//			return qualifiedName;
//		}
//		else if (binding instanceof ITypeBinding){
//			final ITypeBinding typeBinding = (ITypeBinding) binding;
//			
////			 IImportDeclaration import1 = unit.getImport(binding.getName());
////			 if (!import1.exists()){
////				 
////				 try {
////					for (IImportDeclaration importDeclaration : unit.getImports()) {
////						if (importDeclaration.isOnDemand()){
////							
////						}
////					}
////				} catch (JavaModelException e) {
////					// TODO Auto-generated catch block
////					e.printStackTrace();
////				}
////			 }
////				 
//			
//			IJavaElement javaElement = typeBinding.getJavaElement();
//			String packageQ = packageName;
////			while(javaElement != null){
////				if (javaElement instanceof ICompilationUnit) {
////					packageQ = RefactoringUtil.getPackageDeclaration((ICompilationUnit) javaElement);
////					break;
////				}
////				javaElement = javaElement.getParent();
////			}
//			return packageQ + typeBinding.getQualifiedName();
//		}
//		else 
//			return name.getFullyQualifiedName();
//		
//	}

//	private String getPackage(final ITypeBinding typeBinding) {
//		String packageName = typeBinding.getPackage().getName();
//		if (packageName.isEmpty()) packageName = ".";
//		return packageName;
//	}

	public void startVisit() {
		ASTNode root = RefactoringUtil.parseUnit(unit);
		if (root == null)
			return;

		root.accept(this);
	}

	protected void addSearchMatch(SimpleName simpleName) {
		matches.add(new SearchMatch(unit, simpleName.getStartPosition(), simpleName.getLength()));
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
}
