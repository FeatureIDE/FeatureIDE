/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.runtime;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IfStatement;

/**
 * Visitor for AST, currently only responding to the if statement whose begin line number matches the passed line number.
 *
 * @author Matthias Quaas
 *
 */
class IfVisitor extends ASTVisitor {

	int endPosition;
	int startLine;
	CompilationUnit compilationUnit;

	public IfVisitor(final int startLine, final CompilationUnit compilationUnit) {
		super();
		endPosition = 0;
		this.startLine = startLine;
		this.compilationUnit = compilationUnit;
	}

	@Override
	public void endVisit(final IfStatement node) {

		if (compilationUnit.getLineNumber(node.getStartPosition()) == startLine) {
			endPosition = node.getThenStatement().getStartPosition();
			endPosition += node.getThenStatement().getLength();
		}
		super.endVisit(node);

	}

	public int getEndPosition() {
		return endPosition;

	}

}
