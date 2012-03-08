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
import de.ovgu.featureide.core.projectstructure.nodetypes.ProjectTreeNode;


/**
 * This tree represents a Feature Project
 * TODO is this tree still used
 * @author Janet Feigenspan
 */
public class ProjectTree {
	
	/**
	 * This nodes describe the path from the project node to the files.
	 */
	private ArrayList<ProjectTreeNode> projectTreeNodes;
	
	/**
	 * This node represent the files. They are the leaf Nodes of this Tree.
	 */
	private ArrayList<LeafTree> leafTrees;

	/**
	 * creates an empty tree;
	 */
	public ProjectTree() {
		projectTreeNodes = new ArrayList<ProjectTreeNode>();
		leafTrees = new ArrayList<LeafTree>();
		createRoot();
	}

	/**
	 * creates a root node and adds it to the projectTreeNodes.
	 */
	private void createRoot() {
		ProjectTreeNode root = new ProjectTreeNode("root", "root", "root");
		root.setParent(null);
		root.setRoot(true);
		projectTreeNodes.add(root);
	}

	/**
	 * inserts the ProjectTreeNode node in the tree and sets parent as parent of
	 * the node. <br />
	 * insertProjectTreeNode(node, null) is equivalent to
	 * insertProjectTreeNode(ProjectTreeNode node).
	 * 
	 * @param node
	 *            the node that should be inserted
	 * @param parent
	 *            the node that should be the parent of the inserted node
	 */
	public void insertProjectTreeNode(ProjectTreeNode node,
			ProjectTreeNode parent) {
		if (node != null) {
			if (parent != null) {
				node.setParent(parent);
				parent.setChild(node);
				projectTreeNodes.add(node);
			} else
				insertProjectTreeNode(node);
		}
	}

	/**
	 * inserts the ProjectTreeNode node in the tree. Sets the last node in
	 * projectTreeNodes as parent and sets node as child of the last node in
	 * projectTreeNodes. <br />
	 * Convenience method for insertProjectTreeNode (node, parent).
	 * 
	 * @param node
	 *            the node that should be inserted
	 */
	public void insertProjectTreeNode(ProjectTreeNode node) {
		node.setParent(projectTreeNodes.get(projectTreeNodes.size() - 1));
		projectTreeNodes.get(projectTreeNodes.size() - 1).setChild(node);
		projectTreeNodes.add(node);
	}

	/**
	 * inserts the LeafTreeNode node in the tree and sets parent as parent of
	 * the node. <br />
	 * 
	 * @param node
	 *            the node that should be inserted
	 * @param parent
	 *            the node that should be the parent of the inserted node
	 */
	public void insertLeafTreeNode(LeafTree node, ProjectTreeNode parent) {
		if (node == null || parent ==  null) {
			return;
		}
		node.setParent(parent);
		parent.setChild(node);
		leafTrees.add(node);
	}

	/**
	 * Finds a ProjecTreeNode by its name. If no such node is found,
	 * <code> null </code> is returned.
	 * 
	 * @param name
	 *            the name of the node that should be found.
	 * @return the ProjectTreeNode with the name <code> name </code>, or
	 *         <code> null </code>, if no such node is found.
	 */
	public ProjectTreeNode findNodeByName(String name) {
		Iterator<ProjectTreeNode> iterator = projectTreeNodes.iterator();
		while (iterator.hasNext()) {
			ProjectTreeNode node = iterator.next();
			if (node == null || name == null || node.getName() == null) {
				return null;
			}
			if (node.getName().equals(name)) {
				return node;
			}
		}
		return null;
	}

	/**
	 * returns the list of all projectTreeNodes
	 * @return the list of the projectTreeNodes
	 */
	public ArrayList<ProjectTreeNode> getProjectTreeNodes() {
		return projectTreeNodes;
	}

	/**
	 * returns the list of all leafNodes
	 * @return the list of the leafNodes
	 */
	public ArrayList<LeafTree> getLeafTrees() {
		return leafTrees;
	}

	/**
	 * returns the first element in projectTreeNodes, i.e. the root
	 * @return the root of this tree.
	 */
	public ProjectTreeNode getRoot() {
		return projectTreeNodes.get(0);
	}

	/**
	 * starts to print the tree
	 */
	public void print() {
		System.out.println("-------------------------------------------");
		print(getRoot().getChildren().iterator(), "");
		System.out.println("-------------------------------------------");
	}

	/**
	 * recursively prints the tree
	 * @param iterator the iterator for the children
	 * @param space the ammount of space printed for every output line
	 */
	private void print(Iterator<Node> iterator, String space) {
		if (iterator != null) {
			while (iterator.hasNext()) {
				Node node = iterator.next();
				if (node instanceof LeafTree) {
					((LeafTree) node).print(space);
				} else {
					System.out.println(space + node.toString());
					print(((ProjectTreeNode) node).getChildren().iterator(),
							space + "    ");
				}
			}
		}
	}

	/**
	 * deletes all nodes except for the root (actually deletes the root and
	 * creates a new one)
	 */
	public void clear() {
		leafTrees.clear();
		projectTreeNodes.clear();
		createRoot();
	}

	/**
	 * creates an Iterator that traverses all Nodes of this tree
	 * @return the iterator
	 */
	public ProjectTreeIterator iterator(){
		return new ProjectTreeIterator(this);
	}
}
