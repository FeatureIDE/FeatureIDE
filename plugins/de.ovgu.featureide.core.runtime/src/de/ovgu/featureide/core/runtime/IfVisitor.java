package de.ovgu.featureide.core.runtime;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IfStatement;

/**
 * Visitor for AST, currently only responding to the if statement whose begin
 * line number matches the passed line number.
 * 
 * @author Matthias Quaas
 *
 */
class IfVisitor extends ASTVisitor {

	int endPosition;
	int startLine;
	CompilationUnit compilationUnit;

	public IfVisitor(int startLine, CompilationUnit compilationUnit) {
		super();
		endPosition = 0;
		this.startLine = startLine;
		this.compilationUnit = compilationUnit;
	}

	public void endVisit(IfStatement node) {

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