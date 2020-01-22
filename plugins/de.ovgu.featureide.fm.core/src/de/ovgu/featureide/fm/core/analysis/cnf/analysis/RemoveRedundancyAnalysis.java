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
package de.ovgu.featureide.fm.core.analysis.cnf.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.sat4j.specs.IConstr;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ModifiableSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds redundant clauses with respect to a given {@link CNF}. This analysis works by adding every clause group (see {@link AClauseAnalysis}) to the given
 * {@link CNF} at the beginning an then removing and readding each clause group individually. If a clause group is redundant with respect to the current
 * formula, it is marked as redundant and removed completely from the {@link CNF}. Otherwise it is kept as part of the {@link CNF} for the remaining analysis.
 * Clauses are added in the same order a they appear in the given clauses list.<br> For an independent analysis of every clause group use
 * {@link IndependentRedundancyAnalysis}.
 *
 * @author Sebastian Krieter
 *
 * @see AddRedundancyAnalysis
 * @see IndependentRedundancyAnalysis
 */
public class RemoveRedundancyAnalysis extends AClauseAnalysis<List<LiteralSet>> {

	public RemoveRedundancyAnalysis(CNF satInstance) {
		super(satInstance);
	}

	public RemoveRedundancyAnalysis(ISatSolver solver) {
		super(solver);
	}

	public RemoveRedundancyAnalysis(CNF satInstance, List<LiteralSet> clauseList) {
		super(satInstance);
		this.clauseList = clauseList;
	}

	public RemoveRedundancyAnalysis(ISatSolver solver, List<LiteralSet> clauseList) {
		super(solver);
		this.clauseList = clauseList;
	}

	@Override
	protected ISatSolver initSolver(CNF satInstance) {
		try {
			return new ModifiableSatSolver(satInstance);
		} catch (final RuntimeContradictionException e) {
			return null;
		}
	}

	@Override
	public List<LiteralSet> analyze(IMonitor<List<LiteralSet>> monitor) throws Exception {
		if (clauseList == null) {
			return Collections.emptyList();
		}
		if (clauseGroupSize == null) {
			clauseGroupSize = new int[clauseList.size()];
			Arrays.fill(clauseGroupSize, 1);
		}
		monitor.setRemainingWork(clauseGroupSize.length + 1);

		final List<LiteralSet> resultList = new ArrayList<>(clauseGroupSize.length);
		for (int i = 0; i < clauseList.size(); i++) {
			resultList.add(null);
		}

		final List<IConstr> constrs = new ArrayList<>(clauseList.size());
		for (final LiteralSet clause : clauseList) {
			constrs.add(solver.addClause(clause));
		}

		monitor.step();

		int endIndex = 0;
		for (int i = 0; i < clauseGroupSize.length; i++) {
			final int startIndex = endIndex;
			endIndex += clauseGroupSize[i];
			boolean completelyRedundant = true;
			boolean removedAtLeastOne = false;
			for (int j = startIndex; j < endIndex; j++) {
				final IConstr cm = constrs.get(j);
				if (cm != null) {
					removedAtLeastOne = true;
					solver.removeClause(cm);
				}
			}

			if (removedAtLeastOne) {
				for (int j = startIndex; j < endIndex; j++) {
					final LiteralSet clause = clauseList.get(j);

					final SatResult hasSolution = solver.hasSolution(clause.negate());
					switch (hasSolution) {
					case FALSE:
						break;
					case TIMEOUT:
						reportTimeout();
						break;
					case TRUE:
						solver.addClause(clause);
						completelyRedundant = false;
						break;
					default:
						throw new AssertionError(hasSolution);
					}
				}
			}

			if (completelyRedundant) {
				resultList.set(i, clauseList.get(startIndex));
			}
			monitor.step();
		}

		return resultList;
	}

}
