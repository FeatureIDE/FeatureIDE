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
package org.prop4j.analyses;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISatSolver.SatResult;
import org.prop4j.solver.ModifiableSolver;
import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;

import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.remove.FeatureRemover;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class IndeterminedAnalysis extends AbstractAnalysis<int[]> {

	private final List<String> variables;

	public IndeterminedAnalysis(SatInstance satInstance) {
		this(satInstance, null);
	}

	public IndeterminedAnalysis(SatInstance satInstance, List<String> variables) {
		super(satInstance);
		this.variables = variables;
	}

	public IndeterminedAnalysis(ISatSolver solver, List<String> variables) {
		super(solver);
		this.variables = variables;
	}

	@Override
	public int[] analyze(IMonitor monitor) throws Exception {
		monitor.setRemainingWork(variables.size() + 1);

		final VecInt resultList = new VecInt();
		final ModifiableSolver modSolver = new ModifiableSolver(solver.getSatInstance());
		final List<Clause> relevantClauses = new ArrayList<>();

		varLoop: for (final String varName : variables) {
			final Node[] clauses = solver.getSatInstance().getCnf().getChildren();
			final int literal = solver.getSatInstance().getVariable(varName);
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
					final int l = solver.getSatInstance().getSignedVariable((Literal) literals[i]);
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

			try {
				modSolver.addCNF(relevantClauses);
			} catch (final ContradictionException e) {
				continue varLoop;
			}

			final SatResult satResult = modSolver.isSatisfiable();
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
			modSolver.removeLastClauses(relevantClauses.size());

			monitor.step();
		}

		return Arrays.copyOf(resultList.toArray(), resultList.size());
	}

}
