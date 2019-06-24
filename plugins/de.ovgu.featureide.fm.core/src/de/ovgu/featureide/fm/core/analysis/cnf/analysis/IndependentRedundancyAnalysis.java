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
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds redundancies.
 *
 * @author Sebastian Krieter
 */
public class IndependentRedundancyAnalysis extends AClauseAnalysis<List<LiteralSet>> {

	public IndependentRedundancyAnalysis(CNF satInstance) {
		super(satInstance);
	}

	public IndependentRedundancyAnalysis(ISatSolver solver) {
		super(solver);
	}

	public IndependentRedundancyAnalysis(ISatSolver solver, List<LiteralSet> clauseList) {
		super(solver);
		this.clauseList = clauseList;
	}

	public IndependentRedundancyAnalysis(CNF satInstance, List<LiteralSet> clauseList) {
		super(satInstance);
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
		monitor.step();

		int endIndex = 0;
		groupLoop: for (int i = 0; i < clauseGroupSize.length; i++) {
			final int startIndex = endIndex;
			endIndex += clauseGroupSize[i];
			for (int j = startIndex; j < endIndex; j++) {
				final LiteralSet clause = clauseList.get(j);

				final SatResult hasSolution = solver.hasSolution(clause.negate());
				switch (hasSolution) {
				case FALSE:
					resultList.set(i, clause);
					continue groupLoop;
				case TIMEOUT:
					reportTimeout();
					break;
				case TRUE:
					break;
				default:
					throw new AssertionError(hasSolution);
				}
			}
		}

		return resultList;
	}

}
