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
import de.ovgu.featureide.core.projectstructure.nodetypes.TerminalNode;
import de.ovgu.featureide.core.projectstructure.nodetypes.Visitor;


/**
 * This tree represents one file.
 * 
 * @author Janet Feigenspan
 */
public class LeafTree extends Node{
	
	private ArrayList<NonTerminalNode> nonTerminals;
	private ArrayList<TerminalNode> terminals;
	
	private Node parent;

	private String name;

	/**
	 * creates an empty tree; creates a default NonTerminalNode as the root
	 */
	public LeafTree() {
		nonTerminals = new ArrayList<NonTerminalNode>();
		terminals = new ArrayList<TerminalNode>();
		createRoot();
	}

	/**
	 * creates a root node with values root and parent <code>null</code>.
	 */
	private void createRoot() {
		NonTerminalNode root = new NonTerminalNode("LeafTreeRoot", "LeafTreeRoot", "LeafTreeRoot");
		root.setParent(null);
		root.setRoot(true);
		nonTerminals.add(root);
	}

	/**
	 * creates a tree with the NonTerminalNode nonTerminals and the TerminalNode
	 * terminals. Sets the first node in nonTerminals as root.
	 * 
	 * @param nonTerminals
	 *            list of nonterminal nodes
	 * @param terminals
	 *            list of terminal nodes
	 */
	public LeafTree(ArrayList<NonTerminalNode> nonTerminals,
			ArrayList<TerminalNode> terminals) {
		this.nonTerminals = nonTerminals;
		this.terminals = terminals;
		nonTerminals.get(0).setRoot(true);
	}

	public NonTerminalNode getRoot() {
		return nonTerminals.get(0);
	}


	public void setParent(Node parent) {
		this.parent = parent;
	}

	public Node getParent() {
		return parent;
	}

	/**
	 * inserts the NonTerminalNode node in the tree. Sets the child-parent
	 * relationship between node and parent
	 * @param node the node that should be inserted
	 * @param parent the node that should be the parent of node
	 */
	public void insertNonTerminal(NonTerminalNode node, NonTerminalNode parent) {
		node.setParent(parent);
		parent.setChild(node);
		nonTerminals.add(node);
	}

	/**
	 * inserts the TerminalNode node in the tree. Sets the last node in
	 * nonTerminals as parent.
	 * 
	 * @param node
	 *            the node that should be inserted
	 */
	public void insertTerminal(TerminalNode node) {
		this.setParent(node);
		this.setAsChild(node);
		terminals.add(node);
	}

	public void insertTerminal(TerminalNode node, NonTerminalNode parent) {
		node.setParent(parent);
		parent.setChild(node);
		terminals.add(node);
	}

	public ArrayList<NonTerminalNode> getNonTerminals() {
		return nonTerminals;
	}

	public ArrayList<TerminalNode> getTerminals() {
		return terminals;
	}

	/**
	 * finds the Node with the identifier <code> identifier </code>
	 * 
	 * @param identifier
	 *            the identifier of the node that should be found
	 * @return the first NonTerminalNode identified by the identifier or
	 *         <code>null</code>, if that node is not contained in this tree
	 */
	public Node findNode(String identifier) {
		Node node = findNonTerminalNode(identifier);
		if (node != null)
			return node;
		else
			return findTerminalNode(identifier);
	}

	/**
	 * finds the TerminalNode with the identifier <code> identifier </code>
	 * 
	 * @param identifier
	 *            the identifier of the node that should be found
	 * @return the node identified by the identifier or <code>null</code>, if
	 *         that node is not contained in this tree
	 */
	public TerminalNode findTerminalNode(String identifier) {
		Iterator<TerminalNode> iterator = terminals.iterator();
		while (iterator.hasNext()) {
			TerminalNode node = iterator.next();
			if (node.getIdentifier().equals(identifier))
				return node;
		}
		return null;
	}

	/**
	 * finds the NonTerminalNode with the identifier <code> identifier </code>
	 * 
	 * @param identifier
	 *            the identifier of the node that should be found
	 * @return the node identified by the identifier or <code>null</code>, if
	 *         that node is not contained in this tree
	 */
	public NonTerminalNode findNonTerminalNode(String identifier) {
		Iterator<NonTerminalNode> iterator = nonTerminals.iterator();
		while (iterator.hasNext()) {
			NonTerminalNode node = iterator.next();
			if (node.getIdentifier().equals(identifier))
				return node;
		}
		return null;
	}

	/**
	 * sets the last node in nonTerminals as parent node of all nodes contained
	 * in terminals
	 */
	public void setParents() {
		Iterator<TerminalNode> iterator = terminals.iterator();
		while (iterator.hasNext()) {
			iterator.next()
					.setParent(nonTerminals.get(nonTerminals.size() - 1));
		}
	}

	/**
	 * sets the Node node as child of the last node in nonTerminals
	 * 
	 * @param node
	 *            the node that should get a parent
	 */
	public void setAsChild(Node node) {
		nonTerminals.get(nonTerminals.size() - 1).setChild(node);
	}

	/**
	 * sets all nodes contained in terminals as childnode of the last node in
	 * nonterminals
	 */
	public void setChildren() {
		NonTerminalNode parent = nonTerminals.get(nonTerminals.size() - 1);
		Iterator<TerminalNode> iterator = terminals.iterator();
		while (iterator.hasNext())
			parent.setChild(iterator.next());
	}

	/**
	 * returns a list of the children of the NonTerminalNode node
	 * 
	 * @param node
	 *            the of which the children are to be found
	 * @return the list of children
	 */
	public ArrayList<Node> getChildren(NonTerminalNode node) {
		int index = nonTerminals.indexOf(node);
		ArrayList<Node> nodes = new ArrayList<Node>();
		Iterator<NonTerminalNode> iterator = nonTerminals
				.listIterator(index - 1);
		while (iterator.hasNext())
			nodes.add(iterator.next());
		nodes.addAll(nonTerminals.get(nonTerminals.size() - 1).getChildren());
		return nodes;
	}

	public boolean contains(Node node) {
		Iterator<NonTerminalNode> iteratorNT = nonTerminals.iterator();
		while (iteratorNT.hasNext())
			if (iteratorNT.next().getIdentifier().equals(node.getIdentifier()))
				return true;

		Iterator<TerminalNode> iteratorT = terminals.iterator();
		while (iteratorT.hasNext())
			if (iteratorT.next().getIdentifier().equals(node.getIdentifier()))
				return true;

		return false;
	}

	/**
	 * determines the number of nodes in this tree
	 * 
	 * @return the number of all nodes in this tree
	 */
	public int size() {
		return terminals.size() + nonTerminals.size();
	}

	/**
	 * determins the height of this tree (root included)
	 * 
	 * @return the height of this tree
	 */
	public int height() {
		return nonTerminals.size() + 1;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	/**
	 * prints this tree with the given whitespace at the beginning of each line
	 */
	public void print(String space) {
		print(getRoot().getChildren().iterator(), space);
	}

	/**
	 * prints the tree recursively
	 * 
	 * @param iterator
	 *            the iterator for traversing. Contains the chidlren of o node
	 * @param space
	 *            the space left blank before starting to print a node
	 */
	private void print(Iterator<Node> iterator, String space) {
		if (iterator != null) {
			while (iterator.hasNext()) {
				Node node = iterator.next();
				if (node instanceof TerminalNode);
//					CorePlugin.getDefault().logInfo(space + node.toString());
				else {
//					CorePlugin.getDefault().logInfo(space + node.toString());
					print(((NonTerminalNode) node).getChildren().iterator(),
							space + "    ");
				}
			}
		}
	}
	
	/**
	 * deletes all nodes except for the root
	 * (actually deletes the root and creates a new one)
	 */
	public void clear() {
		nonTerminals.clear();
		terminals.clear();
		createRoot();
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);		
	}

	@Override
	public boolean hasChildren() {
		return false;
	}
}
