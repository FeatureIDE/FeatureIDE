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
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.SimpleName;

import de.ovgu.featureide.core.signature.base.AbstractSignature;

/**
 * TODO description
 * 
 * @author steffen
 */
public abstract class AbstractASTVisitor<T extends AbstractSignature> extends ASTVisitor implements IASTVisitor {
	protected final RefactoringSignature refactoringSignature;
	private List<SearchMatch> matches = new ArrayList<>();
	private final ICompilationUnit unit;

	public AbstractASTVisitor(final ICompilationUnit unit, final RefactoringSignature refactoringSignature) {
		this.unit = unit;
		this.refactoringSignature = refactoringSignature;
	}

	@Override
	public List<SearchMatch> getMatches() {
		return matches;
	}

	//	  protected boolean hasSameAsSignatur(String name)
	//	  {
	//		  return hasSameName(name, signature.getName());
	//	  }
	//	  
	protected boolean hasSameName(String name, String otherName) {
		return name.equals(otherName);
	}

	public void startVisit() {
		ASTNode root = RefactoringUtil.parseUnit(unit);
		if (root == null)
			return;

		root.accept(this);
	}

	protected void addSearchMatch(SimpleName simpleName) {
		matches.add(new SearchMatch(unit, simpleName.getStartPosition(), simpleName.getLength()));
	}

	abstract protected <Q extends ASTNode> boolean isSameSignature(T sig1, Q sig2);
}
