package de.ovgu.featureide.featurehouse.refactoring;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;


public interface  IASTVisitor {
	List<ASTNode> getSearchedNodes();
}
