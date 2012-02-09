/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.core.projectstructure.trees;

import java.util.ArrayList;
import java.util.Iterator;

import de.ovgu.featureide.core.projectstructure.nodetypes.Node;
import de.ovgu.featureide.core.projectstructure.nodetypes.NonTerminalNode;
import de.ovgu.featureide.core.projectstructure.nodetypes.ProjectTreeNode;
import de.ovgu.featureide.core.projectstructure.nodetypes.TerminalNode;


/**
 * Traverses the tree. First the inner nodes, then the leaf trees.
 * From each leaf tree first the nonTerminals, then the terminals.
 * 
 * @author Janet Feigenspan
 */
public class ProjectTreeIterator implements Iterator<Node> {
	
	private Node[] nodes;
	private int currentNode;

	public ProjectTreeIterator(ProjectTree projectTree) {
		super();

		// traverse ProjectTreeNodes
		ArrayList<Node> nodesList = new ArrayList<Node>();
		Iterator<ProjectTreeNode> iteratorInner = projectTree.getProjectTreeNodes().iterator();
		while (iteratorInner.hasNext()) {
			nodesList.add(iteratorInner.next());
		}
		
		// traverse Leaftrees
		Iterator<LeafTree> iteratorLeaf = projectTree.getLeafTrees().iterator();
		while (iteratorLeaf.hasNext()) {
			LeafTree leafTree = iteratorLeaf.next();
		
			Iterator<NonTerminalNode> iteratorNonTerminal = leafTree.getNonTerminals().iterator();
			while (iteratorNonTerminal.hasNext())
				nodesList.add(iteratorNonTerminal.next());

			Iterator<TerminalNode> iteratorTerminal = leafTree.getTerminals().iterator();
			while (iteratorTerminal.hasNext())
				nodesList.add(iteratorTerminal.next());
		}
		nodes = new Node[nodesList.size()];
		Iterator<Node> iteratorNodes = nodesList.iterator();
		int i = 0;
		while (iteratorNodes.hasNext()) {
			nodes[i] = iteratorNodes.next();
			i++;
		}
		currentNode = 0;
	}

	public boolean hasNext() {
		return currentNode < nodes.length;
	}

	public Node next() {
		return nodes[currentNode++];
	}

	public void remove() {
	}
	
	public int size() {
		if (nodes != null)
			return nodes.length;
		else return -1;
	}
}
