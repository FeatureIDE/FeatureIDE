package org.prop4j;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * A constraint that is true iff at least one of its children is true.
 * 
 * @author Thomas Th�m
 */
public class Or extends Node {

	public Or(Object ...children) {
		setChildren(children);
	}

	public Or(Node[] children) {
		setChildren(children);
	}

	@Override
	protected Node clausify() {
		for (int i = 0; i < children.length; i++)
			children[i] = children[i].clausify();
		fuseWithSimilarChildren();
//		LinkedList<Node> newNodes = new LinkedList<Node>();
//		createClauseSet(newNodes, new LinkedList<Node>(), children, 0);
//		return new And(newNodes);
		return createCNF(children);
	}
	
	private Node createCNF(Node[] nodes) {
		LinkedList<LinkedList<Node>> clauses = new LinkedList<LinkedList<Node>>();
		clauses.add(new LinkedList<Node>());
		for (Node and : nodes) {
			LinkedList<Node[]> newClauses = new LinkedList<Node[]>();
			for (Node or : and instanceof And ? and.children : new Node[] {and})
				newClauses.add(or instanceof Or ? or.children : new Node[] {or});
			clauses = updateClauses(clauses, newClauses);
		}
		LinkedList<Node> children = new LinkedList<Node>();
		for (LinkedList<Node> clause : clauses)
			children.add(new Or(clause).clone());
		return new And(children);
	}

	private LinkedList<LinkedList<Node>> updateClauses(LinkedList<LinkedList<Node>> clauses,
			LinkedList<Node[]> newClauses) {
		LinkedList<LinkedList<Node>> updatedClauses = new LinkedList<LinkedList<Node>>();
		for (LinkedList<Node> clause : clauses) {
			boolean intersection = false;
			for (Node[] list : newClauses)
				if (containedIn(list, clause)) {
					intersection = true;
					break;
				}
			if (intersection)
				add(updatedClauses, clause);
			else {
				for (Node[] list : newClauses) {
					LinkedList<Node> newClause = clone(clause);
					for (Node node : list)
						newClause.add(node.clone());
					add(updatedClauses, newClause);
				}
			}
		}
		return updatedClauses;
	}

	private void add(LinkedList<LinkedList<Node>> clauses,
			LinkedList<Node> newClause) {
		for (LinkedList<Node> clause : clauses)
			if (containedIn(clause, newClause))
				return;
		clauses.add(newClause);
	}

	private boolean containedIn(LinkedList<Node> clause, LinkedList<Node> newClause) {
		for (Node node : clause)
			if (!newClause.contains(node))
				return false;
		return true;
	}

	private boolean containedIn(Node[] list, LinkedList<Node> clause) {
		for (Node node : list)
			if (!clause.contains(node))
				return false;
		return true;
	}

//	private void createClauseSet(LinkedList<Node> clauses, LinkedList<Node> clause, Node[] nodes, int i) {
//		if (i == nodes.length) {
//			//TO DO check if clause already contained in clauses
//			clauses.add(new Or(clause).clone());
//			return;
//		}
//		Node[] children = nodes[i] instanceof And ?	nodes[i].children : new Node[] { nodes[i] };
//		for (Node node : children) {
//			Node[] children2 = node instanceof Or ? node.children : new Node[] { node };
//			int added = 0;
//			try {
//				for (Node node2 : children2) {
//					Literal literal = (Literal) node2;
//					if (contains(clause, new Literal(literal.var, !literal.positive)))
//						throw new Exception(); //resulting clause is always true
//					if (!contains(clause, literal)) {
//						clause.addLast(literal);
//						added++;
//					}
//				}
//				createClauseSet(clauses, clause, nodes, i+1);
//			} catch (Exception e) {
//			} finally {
//				while (added-- > 0)
//					clause.removeLast();
//			}
//		}
//	}
//
//	private boolean contains(LinkedList<Node> clauses, Node node) {
//		for (Node child : clauses)
//			if (child.equals(node))
//				return true;
//		return false;
//	}
	
	protected void collectChildren(Node node, List<Node> nodes) {
		if (node instanceof Or) {
			for (Node childNode : node.getChildren()) {
				collectChildren(childNode, nodes);
			}
		} else {
			nodes.add(node);
		}
	}
	
	@Override
	public void simplify() {
		List<Node> nodes = new ArrayList<Node>();
		
		for (int i = 0; i < children.length; i++) {
			collectChildren(children[i], nodes);
		}
		
		if (nodes.size() != children.length) {
			Node[] newChildren = nodes.toArray(new Node[nodes.size()]);
			setChildren(newChildren);
		}
		
		super.simplify();
	}
	
	
	@Override
	public Node clone() {
		return new Or(clone(children));
	}

}
