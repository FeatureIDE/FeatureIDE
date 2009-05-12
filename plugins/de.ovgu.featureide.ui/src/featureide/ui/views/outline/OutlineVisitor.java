/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.ui.views.outline;

import java.util.ArrayList;
import java.util.Iterator;

import org.eclipse.core.resources.IFile;

import featureide.core.projectstructure.nodetypes.Node;
import featureide.core.projectstructure.nodetypes.NonTerminalNode;
import featureide.core.projectstructure.nodetypes.ProjectTreeNode;
import featureide.core.projectstructure.nodetypes.TerminalNode;
import featureide.core.projectstructure.nodetypes.Visitor;
import featureide.core.projectstructure.trees.LeafTree;
import featureide.core.projectstructure.trees.ProjectTree;
import featureide.ui.UIPlugin;

/**
 * TODO description
 * 
 * @author Janet Feigenspan
 */
public class OutlineVisitor implements Visitor {

	private IFile input;

	/**
	 * contains the feature, to which <code> input <code> belongs
	 * and the fileName of input;
	 * for finding the according node in the projectTree
	 */
	private String matcher;

	private ArrayList<Node> currentFile;
	int idx = 0;

	private Node[] currentFileNodes;

	private String setMatcher() {
		String[] strings = input.toString().split("/");
		matcher = strings[strings.length - 2] + "/"
				+ strings[strings.length - 1];
		return matcher;
	}

	public OutlineVisitor(IFile input) {
		this.input = input;
		if (this.input != null) {
			matcher = setMatcher();
		}
	}

	public void visit(ProjectTreeNode projectTreeNode) {}

	public void visit(TerminalNode terminalNode) {}

	public void visit(NonTerminalNode nonTerminalNode) {
	}

	private void convertToArray (ArrayList<Node> children) {
		Iterator<Node> iterator = children.iterator();
		currentFileNodes = new Node[children.size()];
		int i = 0;
		while (iterator.hasNext()) {
			currentFileNodes[i] = iterator.next();
			i++;
		}
	}

	@Override
	public void visit(LeafTree leafTreeNode) {
		this.currentFile = leafTreeNode.getRoot().getChildren();
		convertToArray(currentFile);
	}

	public void visitTree(ProjectTree projectTree) {
		Iterator<LeafTree> iterator = projectTree.getLeafTrees().iterator();
		while (iterator.hasNext()) {
			Node node = iterator.next();
			UIPlugin.getDefault().logInfo("machter: " + matcher);
			if (node.getIdentifier().contains(matcher))
				node.accept(this);
		}
	}

	public Node[] getCurrentFile() {
		return currentFileNodes;
	}

}
