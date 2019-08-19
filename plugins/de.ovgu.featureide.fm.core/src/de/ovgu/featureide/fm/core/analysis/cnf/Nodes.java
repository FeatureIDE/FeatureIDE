/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.ErrorLiteral;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order;
import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.CNFSlicer;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Several methods concerning {@link Node} framework.
 *
 * @author Sebastian Krieter
 */
public final class Nodes {

	private Nodes() {}

	public static ClauseList convert(IVariables satInstance, Node node) {
		return convertToCNF(satInstance, node, true);
	}

	public static ClauseList convertToCNF(IVariables satInstance, Node node, boolean keepLiteralOrder) {
		final ClauseList clauses = new ClauseList();
		getClauseFromCNFNode(satInstance, clauses, node, keepLiteralOrder);
		return clauses;
	}

	public static ClauseList convertToDNF(IVariables satInstance, Node node, boolean keepLiteralOrder) {
		final ClauseList clauses = new ClauseList();
		getClauseFromDNFNode(satInstance, clauses, node, keepLiteralOrder);
		return clauses;
	}

	public static CNF convert(Node node) {
		return convertToCNF(node, true);
	}

	public static CNF convertToDNF(Node node) {
		return convertToDNF(node, true);
	}

	public static CNF convertToCNF(Node node, boolean keepLiteralOrder) {
		if (node == null) {
			return null;
		}
		final Set<Object> distinctVariableObjects = getDistinctVariableObjects(node);
		final ArrayList<String> variableList = new ArrayList<>(distinctVariableObjects.size());
		for (final Object varObject : distinctVariableObjects) {
			if (varObject != null) {
				variableList.add(varObject.toString());
			}
		}
		final Variables mapping = new Variables(variableList);
		final List<LiteralSet> clauses = convertToCNF(mapping, node, keepLiteralOrder);
		return new CNF(mapping, clauses);
	}

	public static CNF convertToDNF(Node node, boolean keepLiteralOrder) {
		if (node == null) {
			return null;
		}
		final Set<Object> distinctVariableObjects = getDistinctVariableObjects(node);
		final ArrayList<String> variableList = new ArrayList<>(distinctVariableObjects.size());
		for (final Object varObject : distinctVariableObjects) {
			if (varObject != null) {
				variableList.add(varObject.toString());
			}
		}
		final Variables mapping = new Variables(variableList);
		final List<LiteralSet> clauses = convertToDNF(mapping, node, keepLiteralOrder);
		return new CNF(mapping, clauses);
	}

	public static CNF slice(CNF cnf, Collection<String> errorNames) {
		try {
			return LongRunningWrapper.runMethod(new CNFSlicer(cnf, errorNames));
		} catch (final Exception e) {
			return null;
		}
	}

	public static CNF convertSlicingErrorLiterals(IVariables satInstance, Node cnfNode, boolean keepLiteralOrder) {
		final HashSet<String> varNames = new HashSet<>();
		final HashSet<String> errorNames = new HashSet<>();
		collectVariables(satInstance, cnfNode, varNames, errorNames);

		if (varNames.isEmpty()) {
			return null;
		}

		final ArrayList<String> variableList = new ArrayList<>(satInstance.size() + errorNames.size());
		variableList.addAll(Arrays.asList(satInstance.getNames()).subList(1, satInstance.size() + 1));
		variableList.addAll(errorNames);
		final Variables mappingWithErrors = new Variables(variableList);

		final List<LiteralSet> clauses = convertToCNF(mappingWithErrors, cnfNode, keepLiteralOrder);
		try {
			final CNFSlicer slicer = new CNFSlicer(new CNF(mappingWithErrors, clauses), errorNames);
			final CNF slicedCnf = LongRunningWrapper.runMethod(slicer);
			return slicedCnf == null ? null : new CNF((Variables) satInstance, slicedCnf.getClauses());
		} catch (final Exception e) {
			return null;
		}
	}

	public static void collectVariables(IVariables variables, Node cnfNode, final Set<String> varNames, final Set<String> errorNames) {
		for (final Node clause : cnfNode.getChildren()) {
			final Node[] literals = clause.getChildren();
			for (int i = 0; i < literals.length; i++) {
				final Literal literal = (Literal) literals[i];
				final Object varObject = literal.var;
				if (varObject instanceof String) {
					final String varName = (String) varObject;
					if ((literal instanceof ErrorLiteral) || (variables.getVariable(varName) == 0)) {
						errorNames.add(varName);
					} else {
						varNames.add(varName);
					}
				}
			}
		}
	}

	public static void collectVariables(Node cnfNode, final Set<String> varNames, final Set<String> errorNames) {
		for (final Node clause : cnfNode.getChildren()) {
			final Node[] literals = clause.getChildren();
			for (int i = 0; i < literals.length; i++) {
				final Literal literal = (Literal) literals[i];
				final Object varObject = literal.var;
				if (varObject != null) {
					final String varName = varObject.toString();
					if ((literal instanceof ErrorLiteral)) {
						errorNames.add(varName);
					} else {
						varNames.add(varName);
					}
				}
			}
		}
	}

	public static Set<String> collectVariables(Node cnfNode, final Collection<String> errorNames) {
		final Set<String> varNames = new HashSet<>();
		for (final Node clause : cnfNode.getChildren()) {
			final Node[] literals = clause.getChildren();
			for (int i = 0; i < literals.length; i++) {
				final Literal literal = (Literal) literals[i];
				final Object varObject = literal.var;
				if (varObject instanceof String) {
					final String varName = (String) varObject;
					if ((literal instanceof ErrorLiteral)) {
						if (errorNames != null) {
							errorNames.add(varName);
						}
					} else {
						varNames.add(varName);
					}
				}
			}
		}
		return varNames;
	}

	public static Node convert(CNF satInstance) {
		final List<LiteralSet> clauses = satInstance.getClauses();
		final Or[] nodeClauses = new Or[clauses.size()];
		int index = 0;
		for (final LiteralSet clause : clauses) {
			nodeClauses[index++] = convert(satInstance.getVariables(), clause);
		}
		return new And(nodeClauses);
	}

	public static Or convert(IVariables variables, LiteralSet clause) {
		final int[] literals = clause.getLiterals();
		final Literal[] nodeLiterals = new Literal[literals.length];
		for (int i = 0; i < literals.length; i++) {
			final int literal = literals[i];
			nodeLiterals[i] = new Literal(variables.getName(literal), literal > 0);
		}
		return new Or(nodeLiterals);
	}

	public static Set<Object> getDistinctVariableObjects(Node node) {
		final LinkedHashSet<Object> result = new LinkedHashSet<>();
		getDistinctVariableObjects(node, result);
		return result;
	}

	private static void getDistinctVariableObjects(Node node, Set<Object> result) {
		if (node instanceof Literal) {
			result.add(((Literal) node).var);
		} else {
			for (final Node child : node.getChildren()) {
				getDistinctVariableObjects(child, result);
			}
		}
	}

	static void getClauseFromCNFNode(IVariables s, final Collection<LiteralSet> clauses, final Node node, boolean keepLiteralOrder) {
		final Node cnfNode = Node.buildCNF(node);
		// final Node cnfNode = node.toCNF();
		if (cnfNode instanceof And) {
			for (final Node andChild : cnfNode.getChildren()) {
				clauses.add(getClause(s, andChild, keepLiteralOrder, true));
			}
		} else {
			clauses.add(getClause(s, cnfNode, keepLiteralOrder, true));
		}
	}

	static void getClauseFromDNFNode(IVariables s, final Collection<LiteralSet> clauses, final Node node, boolean keepLiteralOrder) {
		final Node dnfNode = Node.buildDNF(node);
		if (dnfNode instanceof Or) {
			for (final Node orChild : dnfNode.getChildren()) {
				clauses.add(getClause(s, orChild, keepLiteralOrder, false));
			}
		} else {
			clauses.add(getClause(s, dnfNode, keepLiteralOrder, false));
		}
	}

	private static LiteralSet getClause(IVariables s, Node clauseNode, boolean keepLiteralOrder, boolean cnf) {
		int absoluteValueCount = 0;
		boolean valid = true;

		final Literal[] children = (clauseNode instanceof Literal) ? new Literal[] { (Literal) clauseNode }
			: Arrays.copyOf(clauseNode.getChildren(), clauseNode.getChildren().length, Literal[].class);

		for (int j = 0; j < children.length; j++) {
			final Literal literal = children[j];

			// sort out obvious tautologies
			// TODO simplify
			if (cnf) {
				if (literal.var.equals(NodeCreator.varTrue)) {
					if (literal.positive) {
						valid = false;
					} else {
						absoluteValueCount++;
						children[j] = null;
					}
				} else if (literal.var.equals(NodeCreator.varFalse)) {
					if (literal.positive) {
						absoluteValueCount++;
						children[j] = null;
					} else {
						valid = false;
					}
				}
			} else {
				if (literal.var.equals(NodeCreator.varTrue)) {
					if (!literal.positive) {
						valid = false;
					} else {
						absoluteValueCount++;
						children[j] = null;
					}
				} else if (literal.var.equals(NodeCreator.varFalse)) {
					if (!literal.positive) {
						absoluteValueCount++;
						children[j] = null;
					} else {
						valid = false;
					}
				}
			}

		}

		if (valid) {
			if (children.length == absoluteValueCount) {
				throw new RuntimeException("Model is void!");
			}
			final int[] newChildren = new int[children.length - absoluteValueCount];
			int k = 0;
			for (int j = 0; j < children.length; j++) {
				final Literal literal = children[j];
				if (literal != null) {
					final int variable = s.getVariable(literal.var.toString());
					newChildren[k++] = literal.positive ? variable : -variable;
				}
			}
			return new LiteralSet(newChildren, keepLiteralOrder ? Order.UNORDERED : Order.NATURAL);
		} else {
			return null;
		}
	}

}
