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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.ASTNode;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class MethodVisitor {

	protected final FujiMethodSignature signature;
	private final IFile file;
	private final Map<ICompilationUnit, List<ASTNode>> changingNodes = new HashMap<>();
	private final Map<AbstractSignature, IFile> invokedSignatures;
	
	public MethodVisitor(final FujiMethodSignature signature, final IFile file, final Map<AbstractSignature, IFile> invokedSignatures) {
		this.signature = signature;
		this.file = file;
		this.invokedSignatures = invokedSignatures;
	}
	
	public Map<ICompilationUnit, List<ASTNode>> getChangingNodes(){
		return changingNodes;
	}
	
	public void startVisit()
	{
		if ((file == null) || ((file != null) && !file.isAccessible()))  return;
		
		ICompilationUnit unit = JavaCore.createCompilationUnitFrom(file);
		if (unit == null) return;
		
		ASTNode root = RefactoringUtil.parseUnit(unit);
		if (root == null) return;
		
		final AbstractASTVisitor<FujiMethodSignature> visitor = new MethodDeclarationVisitor(signature);
		root.accept(visitor);
		
		changingNodes.put(unit, visitor.getSearchedNodes());
		
		for (Entry<AbstractSignature, IFile> invokedSignature : invokedSignatures.entrySet()) {
			final IFile file = invokedSignature.getValue();
			if ((file == null) || ((file != null) && !file.isAccessible()))  return;
			
			unit = JavaCore.createCompilationUnitFrom(file);
			if (unit == null) return;
			
			root = RefactoringUtil.parseUnit(unit);
			if (root == null) return;
			
			final MethodInvocationVisitor expVisitor = new MethodInvocationVisitor(signature);
			root.accept(expVisitor);
			
			changingNodes.put(unit, expVisitor.getSearchedNodes());
		}
	}

	
}
