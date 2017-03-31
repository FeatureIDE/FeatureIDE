/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package org.prop4j;

import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_SUPPORTING_THIS_METHOD;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * A propositional node that can be transformed into conjunctive normal form
 * (cnf).
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public abstract class Node {

	protected Node[] children;

	@SuppressWarnings("unchecked")
	public void setChildren(Object... newChildren) {
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

	/**
	 * Returns true iff this is in conjunctive normal form.
	 * This is the case iff this is a conjunction of disjunctions of literals.
	 * Note that redundant nodes may be omitted.
	 * This means that instead of one-literal conjunctions and disjunctions, the literal alone may be stored.
	 * @return true iff this is in conjunctive normal form.
	 */
	public abstract boolean isConjunctiveNormalForm();
	
	/**
	 * Returns true iff this is in clausal normal form.
	 * This is a more narrow case of conjunctive normal form.
	 * Specifically, redundant nodes may not be omitted.
	 * In other words, this must be a conjunction of clauses.
	 * Each clause must in turn contain nothing but a positive amount of literals.
	 * @return true iff this is in clausal normal form
	 */
	public abstract boolean isClausalNormalForm();

	public Node toCNF() {
		Node cnf = this;
		cnf = cnf.eliminateNonCNFOperators();
		cnf = deMorgan(cnf);
		return cnf.clausify();
	}

	public Node toRegularCNF() {
		Node regularCNFNode = this.toCNF();
		if (regularCNFNode instanceof And) {
			final Node[] children = regularCNFNode.getChildren();
			for (int i = 0; i < children.length; i++) {
				final Node child = children[i];
				if (child instanceof Literal) {
					children[i] = new Or(child);
				}
			}
		} else if (regularCNFNode instanceof Or) {
			regularCNFNode = new And(regularCNFNode);
		} else if (regularCNFNode instanceof Literal) {
			regularCNFNode = new And(new Or(regularCNFNode));
		}
		return regularCNFNode;
	}

	public boolean getValue(Map<Object, Boolean> map) {
		throw new RuntimeException(getClass().getName() + IS_NOT_SUPPORTING_THIS_METHOD);
	}

	public static Node buildCNF(Node node) {
		Node cnf = node.eliminateNonCNFOperators();
		cnf = deMorgan(cnf);
		cnf = buildCNF_rec(cnf);
		return cnf;
	}

	protected final Node eliminateNonCNFOperators() {
		if (children != null) {
			final Node[] newChildren = new Node[children.length];
			for (int i = 0; i < children.length; i++) {
				newChildren[i] = children[i].eliminateNonCNFOperators();
			}
			return eliminateNonCNFOperators(newChildren);
		} else {
			return eliminateNonCNFOperators(null);
		}
	}

	protected abstract Node eliminateNonCNFOperators(Node[] newChildren);

	private static Node deMorgan(Node node) {
		if (node instanceof Literal) {
			return node;
		} else if (node instanceof Not) {
			final Node notChild = node.getChildren()[0];
			if (notChild instanceof Literal) {
				final Literal clone = (Literal) notChild.clone();
				clone.flip();
				return clone;
			} else if (notChild instanceof Not) {
				return deMorgan(notChild.getChildren()[0]);
			} else if (notChild instanceof Or) {
				final Node[] children = notChild.getChildren();
				final Node[] newChildren = new Node[children.length];
				for (int i = 0; i < children.length; i++) {
					newChildren[i] = deMorgan(new Not(children[i]));
				}
				return new And(newChildren);
			} else {
				final Node[] children = notChild.getChildren();
				final Node[] newChildren = new Node[children.length];
				for (int i = 0; i < children.length; i++) {
					newChildren[i] = deMorgan(new Not(children[i]));
				}
				return new Or(newChildren);
			}
		} else {
			final Node[] children = node.getChildren();
			for (int i = 0; i < children.length; i++) {
				children[i] = deMorgan(children[i]);
			}
			return node;
		}
	}

	private static Node buildCNF_rec(Node node) {
		if (node instanceof Literal) {
			return node;
		} else if (node instanceof Or) {
			final ArrayList<Node> newChildren = new ArrayList<>();
			Node[] children = node.getChildren();
			boolean containsAnd = false;
			for (int i = 0; i < children.length; i++) {
				final Node newNode = buildCNF_rec(children[i]);
				if (newNode != null) {
					if (newNode instanceof And) {
						containsAnd = true;
						newChildren.add(newNode);
					} else if (newNode instanceof Or) {
						newChildren.addAll(Arrays.asList(newNode.getChildren()));
					} else {
						newChildren.add(newNode);
					}
				}
			}

			if (containsAnd) {
				final int[][] sizeArrays = new int[newChildren.size()][];
				children = null;
				node.setChildren(null);
				for (int i = 0; i < newChildren.size(); i++) {
					final Node newChild = newChildren.get(i);
					if (newChild instanceof And) {
						final Node[] newChildChildren = newChild.getChildren();
						final int[] curSizeArray = new int[newChildChildren.length];
						sizeArrays[i] = curSizeArray;
						for (int j = 0; j < newChildChildren.length; j++) {
							final Node child = newChildChildren[j];
							curSizeArray[j] = (child instanceof Or) ? child.getChildren().length : -1;
						}
					} else {
						sizeArrays[i] = null;
					}
				}
				final HashSet<Node> newCleanChildren = new HashSet<>();

				final int[] indexArray = new int[newChildren.size()];
				boolean carry;
				do {
					carry = true;
					int sum = 0;
					for (int i = 0; i < sizeArrays.length; i++) {
						final int[] curSizeArray = sizeArrays[i];
						if (curSizeArray != null) {
							int index = indexArray[i];
							if (carry) {
								index++;
								if (index >= curSizeArray.length) {
									index = 0;
									carry = true;
								} else {
									carry = false;
								}
								indexArray[i] = index;
							}
							sum += Math.abs(curSizeArray[index]);
						} else {
							sum++;
						}
					}

					final Node[] newClause = new Node[sum];
					int curIndex = 0;
					for (int i = 0; i < sizeArrays.length; i++) {
						final Node newChild = newChildren.get(i);
						final int[] curSizeArray = sizeArrays[i];

						if (curSizeArray != null) {
							int index = indexArray[i];
							final Node newChildChild = newChild.getChildren()[index];
							if (curSizeArray[index] < 0) {
								newClause[curIndex++] = newChildChild;
							} else {
								final Node[] newChildChildChildren = newChildChild.getChildren();
								System.arraycopy(newChildChildChildren, 0, newClause, curIndex, newChildChildChildren.length);
								curIndex += newChildChildChildren.length;
							}
						} else {
							newClause[curIndex++] = newChild;
						}
					}

					newCleanChildren.add(new Or(newClause));
				} while (!carry);
				return new And(newCleanChildren);
			} else {
				node.setChildren(newChildren.toArray(new Node[newChildren.size()]));
				return node;
			}
		} else {
			final ArrayList<Node> newChildren = new ArrayList<>();
			final Node[] children = node.getChildren();
			for (int i = 0; i < children.length; i++) {
				final Node newNode = buildCNF_rec(children[i]);
				if (newNode != null) {
					if (newNode instanceof And) {
						newChildren.addAll(Arrays.asList(newNode.getChildren()));
					} else {
						newChildren.add(newNode);
					}
				}
			}
			node.setChildren(newChildren.toArray(new Node[newChildren.size()]));
			return node;
		}
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
	public int hashCode() {
		int hashCode = children.length * 37;
		for (int i = 0; i < children.length; i++) {
			hashCode += children[i].hashCode();
		}
		return hashCode;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object) {
			return true;
		}
		if (!getClass().isInstance(object)) {
			return false;
		}
		Node otherNode = (Node) object;
		if (children.length != otherNode.children.length) {
			return false;
		}
		final List<Node> thisChildrenList = Arrays.asList(children);
		final List<Node> otherChildrenList = Arrays.asList(otherNode.children);
		return thisChildrenList.containsAll(otherChildrenList) && otherChildrenList.containsAll(thisChildrenList);
	}

	@Override
	public String toString() {
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
	 * @param symbols the symbols for logical connectors
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

	@SuppressWarnings("unchecked")
	protected Node eliminate(Class<? extends Node>... array) {
		return eliminate(Arrays.asList(array));
	}

	protected Node eliminate(List<Class<? extends Node>> list) {
		for (int i = 0; i < children.length; i++)
			children[i] = children[i].eliminate(list);
		return this;
	}

	protected Node clausify() {
		throw new RuntimeException(getClass().getName() + IS_NOT_SUPPORTING_THIS_METHOD);
	}

	public List<Node> replaceFeature(IFeature feature, IFeature replaceWithFeature) {
		return replaceFeature(feature, replaceWithFeature, new LinkedList<Node>());
	}

	public List<Node> replaceFeature(IFeature feature, IFeature replaceWithFeature, List<Node> list) {
		if (this instanceof Literal) {
			if (((Literal) this).var.equals(feature.getName())) {
				((Literal) this).var = replaceWithFeature.getName();
				list.add(this);
			}
		} else {
			for (Node child : this.children) {
				child.replaceFeature(feature, replaceWithFeature, list);
			}
		}
		return list;
	}

	protected final void fuseWithSimilarChildren() {
		int count = children.length;
		for (Node child : children) {
			if (getClass().isInstance(child)) {
				count += child.children.length - 1;
			}
		}
		final Node[] newChildren = new Node[count];
		int i = 0;
		for (Node child : children) {
			if (getClass().isInstance(child)) {
				System.arraycopy(child.children, 0, newChildren, i, child.children.length);
				i += child.children.length;
			} else {
				newChildren[i++] = child;
			}
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
			} else {
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

	public List<String> getContainedFeatures() {
		List<String> ret = new ArrayList<>();
		getContainedFeatures(this, ret);
		return ret;
	}

	private void getContainedFeatures(Node actNode, List<String> featureList) {
		if (actNode instanceof Literal) {
			featureList.add(((Literal) actNode).var.toString());
		} else {
			for (Node child : actNode.getChildren()) {
				getContainedFeatures(child, featureList);
			}
		}
	}

	/**
	 * Returns all literals contained in this node and its children.
	 * @return all literals contained in this node and its children
	 */
	public Set<Literal> getLiterals() {
		final Set<Literal> literals = new LinkedHashSet<>();
		if (this instanceof Literal) {
			literals.add((Literal) this);
		}
		if (children == null) {
			return literals;
		}
		for (int i = 0; i < children.length; i++) {
			literals.addAll(children[i].getLiterals());
		}
		return literals;
	}
}
