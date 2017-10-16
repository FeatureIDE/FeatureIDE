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
package de.ovgu.featureide.fm.core.analysis.cnf.analysis;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.SatUtils;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds redundancies by incrementally adding constraints.<br/> <b>Note:</b> This analysis might be faster than {@link RedundancyAnalysis}, which uses removal
 * of constraints. However, this analysis only checks the redundancy of each constraint at the time of adding it to the formula. Thus, it cannot detect
 * constraints that become redundant by the adding another constraint later on.
 *
 * @author Sebastian Krieter
 */
public class RedundancyAnalysis2 extends AClauseAnalysis<List<LiteralSet>> {

	public RedundancyAnalysis2(CNF satInstance) {
		super(satInstance);
	}

	public RedundancyAnalysis2(ISatSolver solver) {
		super(solver);
	}

	public RedundancyAnalysis2(CNF satInstance, List<LiteralSet> clauseList) {
		super(satInstance);
		this.clauseList = clauseList;
	}

	public RedundancyAnalysis2(ISatSolver solver, List<LiteralSet> clauseList) {
		super(solver);
		this.clauseList = clauseList;
	}

	@Override
	public List<LiteralSet> analyze(IMonitor monitor) throws Exception {
		if (clauseList == null) {
			return Collections.emptyList();
		}
		if (clauseGroupSize == null) {
			clauseGroupSize = new int[clauseList.size()];
			Arrays.fill(clauseGroupSize, 1);
		}
		monitor.setRemainingWork(clauseList.size() + 1);

		final List<LiteralSet> resultList = new ArrayList<>(clauseGroupSize.length);
		for (int i = 0; i < clauseList.size(); i++) {
			resultList.add(null);
		}
		// TODO Find a better way of sorting
		// final Integer[] index = Functional.getSortedIndex(resultList, new ClauseLengthComparatorDsc());
		monitor.step();

		int endIndex = 0;
		for (int i = 0; i < clauseGroupSize.length; i++) {
			final int startIndex = endIndex;
			endIndex += clauseGroupSize[i];
			boolean completelyRedundant = true;
			for (int j = startIndex; j < endIndex; j++) {
				final LiteralSet clause = clauseList.get(j);
				final SatResult hasSolution = solver.hasSolution(SatUtils.negateSolution(clause.getLiterals()));
				switch (hasSolution) {
				case FALSE:
					break;
				case TIMEOUT:
					reportTimeout();
				case TRUE:
					solver.addClause(clause);
					completelyRedundant = false;
					break;
				default:
					throw new AssertionError(hasSolution);
				}
			}
			if (completelyRedundant) {
				resultList.set(i, clauseList.get(startIndex));
			}
		}

		return resultList;
	}

}
