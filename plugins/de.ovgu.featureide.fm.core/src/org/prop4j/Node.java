/* Prop4J - A Library for Propositional Formulas
 * Copyright (C) 2007-2013  Prop4J team, University of Magdeburg, Germany
 *
 * This file is part of Prop4J.
 * 
 * Prop4J is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * Prop4J is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with Prop4J.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/prop4j/ for further information.
 */
package org.prop4j;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.Feature;

/**
 * A propositional node that can be transformed into conjunctive normal form
 * (cnf).
 * 
 * @author Thomas Thuem
 */
public abstract class Node {
	
	protected Node[] children;

	@SuppressWarnings("unchecked")
	public void setChildren(Object ...newChildren) {
		//allow collections as parameters
		if (newChildren.length == 1 && newChildren[0] instanceof Collection)
			newChildren = ((Collection<Object>) newChildren[0]).toArray();
		//copy children and create literals
		children = new Node[newChildren.length];
		for (int i = 0; i < children.length; i++)
			children[i] = getNode(newChildren[i]);
	}
	
	public void setChildren(Object leftChild, Object rightChild) {
		children = new Node[] { getNode(leftChild), getNode(rightChild) };
	}

	public void setChildren(Node[] newChildren) {
		children = newChildren;
	}
	
	public Node[] getChildren() {
		return children;
	}
	
	@SuppressWarnings("unchecked")
	public Node toCNF() {
		Node node = this;
		node = node.eliminate(Choose.class, Equals.class, Implies.class);
		node = node.eliminate(Not.class);
		node = node.eliminate(AtMost.class, AtLeast.class);
		node = node.eliminate(Not.class);
		return node.clausify();
	}
	
	@SuppressWarnings("unchecked")
	public Node eliminateNotSupportedSymbols(final String[] symbols) {
		Node node = this;
		for (int i = 0; i < symbols.length; i++) {
			if (symbols[i].equals(NodeWriter.noSymbol)) {
				switch (i) {
					case 0:
						node = node.eliminate(Not.class);
						break;
					case 1:
						node = node.eliminate(And.class);
						break;
					case 2:
						node = node.eliminate(Or.class);
						break;
					case 3:
						node = node.eliminate(Implies.class);
						break;
					case 4:
						node = node.eliminate(Equals.class);
						break;
					case 6:
						node = node.eliminate(Choose.class);
						break;
					case 7:
						node = node.eliminate(AtLeast.class);
						break;
					case 8:
						node = node.eliminate(AtMost.class);
						break;
					default:
						break;
				}
			}
		}
		return node;
	}

	@SuppressWarnings("unchecked")
	public Node toCNFprintln() {
		Node node = this;
		System.out.println(node);
		node = node.eliminate(Choose.class, Equals.class, Implies.class);
		System.out.println(node);
		node = node.eliminate(Not.class);
		System.out.println(node);
		node = node.eliminate(AtMost.class, AtLeast.class);
		System.out.println(node);
		node = node.eliminate(Not.class);
		System.out.println(node);
		node = node.clausify();
		System.out.println(node);
		System.out.println();
		return node;
	}
	
	public void simplify() {
		for (int i = 0; i < children.length; i++) {
			children[i].simplify();
		}
	}

	abstract public Node clone();

	@Override
	public boolean equals(Object object) {
		if (!getClass().isInstance(object))
			return false;
		Node otherNode = (Node) object;
		if (children.length != otherNode.children.length)
			return false;
		for (int i = 0; i < children.length; i++) {
			boolean pairFound = false;
			for (int j = 0; j < otherNode.children.length; j++)
				if (pairFound = children[i].equals(otherNode.children[j]))
					break;
			if (!pairFound)
				return false;
		}
		return true;
	}

	@Override
	public String toString() 
	{
		return NodeWriter.nodeToString(this);
	}

	/**
	 * Returns a string representation of this node. The symbols for logical
	 * connectors, e.g. And, are given as a parameter.
	 * 
	 * @see org.prop4j.NodeWriter.shortSymbols (default)
	 * @see org.prop4j.NodeWriter.logicalSymbols
	 * @see org.prop4j.NodeWriter.textualSymbols
	 * 
	 * @param  symbols  the symbols for logical connectors
	 * 
	 * @return a string representing this node
	 */
	public String toString(String[] symbols) {
		return NodeWriter.nodeToString(this, symbols, false, true);
	}

	public static Node[] clone(Node[] array) {
		Node[] newArray = new Node[array.length];
		for (int i = 0; i < newArray.length; i++)
			newArray[i] = array[i].clone();
		return newArray;
	}

	public static LinkedList<Node> clone(LinkedList<Node> list) {
		LinkedList<Node> newList = new LinkedList<Node>();
		for (Node node : list)
			newList.add(node.clone());
		return newList;
	}

	protected Node eliminate(Class<? extends Node> ...array) {
		return eliminate(Arrays.asList(array));
	}
	
	protected Node eliminate(List<Class<? extends Node>> list) {
		for (int i = 0; i < children.length; i++)
			children[i] = children[i].eliminate(list);
		return this;
	}
	
	protected Node clausify() {
		throw new RuntimeException(getClass().getName() + " is not supporting this method");
	}

	public List<Node> replaceFeature(Feature feature, Feature replaceWithFeature)
	{
		return replaceFeature(feature, replaceWithFeature, new LinkedList<Node>());	
	}	
	
	public List<Node> replaceFeature(Feature feature, Feature replaceWithFeature, List<Node> list)
	{
		if (this instanceof Literal)
		{
			if (((Literal)this).var.equals(feature.getName())) 
			{
				((Literal)this).var = replaceWithFeature.getName();
				list.add(this);
			}
		}else
		{
			for (Node child : this.children)
			{
				child.replaceFeature(feature, replaceWithFeature, list);
			}
		}
		return list;
	}
	
	protected void fuseWithSimilarChildren() {
		int count = children.length;
		for (Node child : children)
			if (getClass().isInstance(child))
				count += child.children.length - 1;
		Node[] newChildren = new Node[count];
		int i = 0;
		for (Node child : children) {
			if (getClass().isInstance(child))
				for (Node childsChild : child.children)
					newChildren[i++] = childsChild;
			else
				newChildren[i++] = child;
		}
		children = newChildren;
	}
	
	protected static Node getNode(Object object) {
		return object instanceof Node ? (Node) object : new Literal(object);
	}
	
	protected Node[] chooseKofN(Node[] elements, int k, boolean negated) {
		int n = elements.length;

		//return tautology
		if (k == 0 || k == n + 1)
			return new Node[] { new Or(new Not(elements[0].clone()), elements[0].clone()) };

		//return contradiction
		if (k < 0 || k > n + 1)
			return new Node[] { new And(new Not(elements[0].clone()), elements[0].clone()) };

		Node[] newNodes = new Node[binom(n, k)];
		int j = 0;

		//negate all elements
		if (negated)
			negateNodes(elements);
		
		Node[] clause = new Node[k];
		int[] index = new int[k];

		//the position that is currently filled in clause
		int level = 0; 
		index[level] = -1;
		
		while (level >= 0) {
			//fill this level with the next element
			index[level]++;
			//did we reach the maximum for this level
			if (index[level] >= n - (k - 1 - level)) {
				//go to previous level
				level--;
			}
			else {
				clause[level] = elements[index[level]];
				if (level == k - 1)
					newNodes[j++] = new Or(clone(clause));
				else {
					//go to next level
					level++;
					//allow only ascending orders (to prevent from duplicates)
					index[level] = index[level - 1];
				}
			}
		}
		if (j != newNodes.length)
			throw new RuntimeException("Pre-calculation of the number of elements failed!");
		return newNodes;
	}

	public static int binom(int n, int k) {
		if (k > n / 2)
			k = n - k;
		if (k < 0 || n < 0)
			return 0;
		if (k == 0 || n == 0)
			return 1;
		return binom(n - 1, k - 1) * n / k;
	}
	
	protected static void negateNodes(Node[] nodes) {
		for (int i = 0; i < nodes.length; i++)
			nodes[i] = new Not(nodes[i]);
	}
	

}