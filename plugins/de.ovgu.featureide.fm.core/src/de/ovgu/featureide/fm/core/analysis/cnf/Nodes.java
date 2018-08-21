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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.ErrorLiteral;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.CNFSlicer;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Several methods concerning {@link Node} framework.
 *
 * @author Sebastian Krieter
 */
public final class Nodes {

	private Nodes() {}

	public static ClauseList convert(IVariables satInstance, Node node) {
		final ClauseList clauses = new ClauseList();
		CNFCreator.getClauseFromNode(satInstance, clauses, node);
		return clauses;
	}

	public static CNF convert(Node node) {
		final Set<Object> distinctVariableObjects = getDistinctVariableObjects(node);
		final ArrayList<String> variableList = new ArrayList<>(distinctVariableObjects.size());
		for (final Object varObject : distinctVariableObjects) {
			if (varObject instanceof String) {
				variableList.add((String) varObject);
			}
		}
		final Variables mapping = new Variables(variableList);
		final List<LiteralSet> clauses = convert(mapping, node);
		return new CNF(mapping, clauses);
	}

	public static CNF convertSlicingError(IVariables satInstance, Node cnfNode) {
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

		final List<LiteralSet> clauses = convert(mappingWithErrors, cnfNode);
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

	public static Set<Object> getDistinctVariableObjects(Node cnf) {
		final HashSet<Object> result = new HashSet<>();
		for (final Node clause : cnf.getChildren()) {
			final Node[] literals = clause.getChildren();
			for (int i = 0; i < literals.length; i++) {
				result.add(((Literal) literals[i]).var);
			}
		}
		return result;
	}

}
