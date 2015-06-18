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

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.signature.base.AbstractSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class RefactoringSignature {
	private AbstractSignature declaration;
	
	private Set<AbstractSignature> invocations = new HashSet<>();
	
	private final IFile file;
	
	private boolean renameDeclaration = false;
	
	public RefactoringSignature(final IFile file, final AbstractSignature declaration) {
		this.file = file;
		this.declaration = declaration;
	}
	
	public IFile getFile() {
		return file;
	}
	
	public AbstractSignature getDeclaration() {
		return declaration;
	}

	public void setDeclaration(AbstractSignature declaration) {
		this.declaration = declaration;
	}

	public Set<AbstractSignature> getInvocations() {
		return invocations;
	}

	public void addInvocation(AbstractSignature invocation) {
		this.invocations.add(invocation);
	}
	
	@Override
	public String toString() {
		
		return "File: " + file + "; declaration: " + declaration + "; invocations: " + invocations;
	}

	public boolean isRenameDeclaration() {
		return renameDeclaration;
	}

	/**
	 * @param renameDeclaration the renameDeclaration to set
	 */
	public void setRenameDeclaration(boolean renameDeclaration) {
		this.renameDeclaration = renameDeclaration;
	}

}
