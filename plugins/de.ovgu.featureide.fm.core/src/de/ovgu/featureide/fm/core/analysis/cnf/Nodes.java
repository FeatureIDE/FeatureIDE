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

	public static CNF convert(Node node) {
		if (node == null) {
			return null;
		}
		return convertNF(node.toRegularCNF(), true, true);
	}

	public static ClauseList convert(Variables satInstance, Node node) {
		return convert(satInstance, node, true);
	}

	public static ClauseList convert(Variables satInstance, Node node, boolean keepLiteralOrder) {
		if (node == null) {
			return null;
		}
		return convertNF(satInstance, node.toRegularCNF(), keepLiteralOrder, true);
	}

	public static CNF convertDNF(Node node) {
		return convertNF(node, true, true);
	}

	public static CNF convertCNF(Node node) {
		return convertNF(node, true, false);
	}

	public static CNF convertNF(Node node, boolean keepLiteralOrder, boolean cnf) {
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
		final List<LiteralSet> clauses = convertNF(mapping, node, keepLiteralOrder, cnf);
		return new CNF(mapping, clauses);
	}

	public static ClauseList convertNF(Variables satInstance, Node node, boolean keepLiteralOrder, boolean cnf) {
		final ClauseList clauses = new ClauseList();
		getClauseFromNode(satInstance, clauses, node, keepLiteralOrder, cnf);
		return clauses;
	}

	public static CNF slice(CNF cnf, Collection<String> errorNames) {
		try {
			return LongRunningWrapper.runMethod(new CNFSlicer(cnf, errorNames));
		} catch (final Exception e) {
			return null;
		}
	}

	public static CNF convertSlicingErrorLiterals(Variables satInstance, Node cnfNode, boolean keepLiteralOrder) {
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

		final List<LiteralSet> clauses = convertNF(mappingWithErrors, cnfNode, keepLiteralOrder, true);
		try {
			final CNFSlicer slicer = new CNFSlicer(new CNF(mappingWithErrors, clauses), errorNames);
			final CNF slicedCnf = LongRunningWrapper.runMethod(slicer);
			return slicedCnf == null ? null : new CNF((Variables) satInstance, slicedCnf.getClauses());
		} catch (final Exception e) {
			return null;
		}
	}

	public static void collectVariables(Variables variables, Node cnfNode, final Set<String> varNames, final Set<String> errorNames) {
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

	public static Or convert(Variables variables, LiteralSet clause) {
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

	static void getClauseFromNode(Variables s, final Collection<LiteralSet> clauses, final Node node, boolean keepLiteralOrder, boolean cnf) {
		for (final Node children : node.getChildren()) {
			final LiteralSet clause = getClause(s, children, keepLiteralOrder, cnf);
			if (clause != null) {
				if (clause.isEmpty()) {
					clauses.clear();
					clauses.add(new LiteralSet(0));
					return;
				} else {
					clauses.add(clause);
				}
			}
		}
	}

	private static LiteralSet getClause(Variables s, Node clauseNode, boolean keepLiteralOrder, boolean cnf) {
		int absoluteValueCount = 0;
		boolean irrelevant = false;

		final Literal[] children = (clauseNode instanceof Literal) ? new Literal[] { (Literal) clauseNode }
			: Arrays.copyOf(clauseNode.getChildren(), clauseNode.getChildren().length, Literal[].class);

		for (int j = 0; j < children.length; j++) {
			final Literal literal = children[j];

			// sort out obvious tautologies
			// TODO simplify
			if (cnf) {
				if (literal.var.equals(NodeCreator.varTrue)) {
					if (literal.positive) {
						irrelevant = true;
					} else {
						absoluteValueCount++;
						children[j] = null;
					}
				} else if (literal.var.equals(NodeCreator.varFalse)) {
					if (literal.positive) {
						absoluteValueCount++;
						children[j] = null;
					} else {
						irrelevant = true;
					}
				}
			} else {
				if (literal.var.equals(NodeCreator.varTrue)) {
					if (!literal.positive) {
						irrelevant = true;
					} else {
						absoluteValueCount++;
						children[j] = null;
					}
				} else if (literal.var.equals(NodeCreator.varFalse)) {
					if (!literal.positive) {
						absoluteValueCount++;
						children[j] = null;
					} else {
						irrelevant = true;
					}
				}
			}
		}

		if (irrelevant) {
			return null;
		} else {
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
		}
	}

}
