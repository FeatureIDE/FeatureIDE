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
package org.prop4j.analyses.impl.general;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.analyses.GeneralSolverAnalysis;
import org.prop4j.solver.ISatResult;
import org.prop4j.solver.ISolver;
import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.remove.FeatureRemover;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 * @author Joshua Sprey
 */
public class IndeterminedAnalysis extends GeneralSolverAnalysis<int[]> {

	private List<String> variables;

	public IndeterminedAnalysis(ISolver solver, List<String> variables) {
		super(solver);
		this.variables = variables;
	}

	public IndeterminedAnalysis(ISolver solver) {
		super(solver);
	}

	public void init(List<String> variables) {
		this.variables = variables;
	}

	@Override
	public int[] analyze(IMonitor monitor) {
		if (variables.isEmpty()) {
			return null;
		}

		monitor.setRemainingWork(variables.size() + 1);

		final VecInt resultList = new VecInt();
		final List<Clause> relevantClauses = new ArrayList<>();

		varLoop: for (final String varName : variables) {
			final Node[] clauses = solver.getProblem().getRoot().getChildren();
			final int literal = solver.getProblem().getIndexOfVariable(varName);
			relevantClauses.clear();

			final ArrayList<String> removeVar = new ArrayList<>(variables);
			removeVar.remove(varName);
			final FeatureRemover remover = new FeatureRemover(new And(clauses), removeVar, false, true);
			final Node newClauseList = remover.createNewClauseList(LongRunningWrapper.runMethod(remover));

			for (final Node clause : newClauseList.getChildren()) {
				final Node[] literals = clause.getChildren();

				final VecInt newLiterals = new VecInt();
				boolean relevant = false;

				for (int i = 0; i < literals.length; i++) {
					final int l = solver.getProblem().getSignedIndexOfVariable((Literal) literals[i]);
					if (Math.abs(l) == literal) {
						relevant = true;
					} else {
						newLiterals.push(l);
					}
				}

				if (relevant) {
					if (newLiterals.isEmpty()) {
						continue varLoop;
					} else {
						relevantClauses.add(new Clause(Arrays.copyOf(newLiterals.toArray(), newLiterals.size())));
					}
				}
			}

			solver.push(getNodeArray(relevantClauses));

			final ISatResult satResult = solver.isSatisfiable();
			switch (satResult) {
			case FALSE:
			case TIMEOUT:
				break;
			case TRUE:
				resultList.push(literal);
				break;
			default:
				throw new AssertionError(satResult);
			}
			solver.pop(relevantClauses.size());

			monitor.step();
		}

		return Arrays.copyOf(resultList.toArray(), resultList.size());
	}

	private Node[] getNodeArray(List<Clause> clauses) {
		final Node[] nodes = new Node[clauses.size()];
		for (int j = 0; j < clauses.size(); j++) {
			final Clause clause = clauses.get(j);
			final Node[] clauseLiteralNodes = new Node[clause.getLiterals().length];
			for (int i = 0; i < clause.getLiterals().length; i++) {
				final Literal literalNode = new Literal(solver.getProblem().getVariableOfIndex(clause.getLiterals()[i]));
				literalNode.positive = clause.getLiterals()[i] > 0;
				clauseLiteralNodes[i] = literalNode;
			}
			final Node clauseNode = new Or(clauseLiteralNodes);
			nodes[j] = clauseNode;
		}
		return nodes;
	}

}
