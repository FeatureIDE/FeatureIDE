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
package de.ovgu.featureide.fm.core.analysis.cnf.generator;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AbstractAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Determines whether a sat instance is satisfiable and returns the found model.
 *
 * @author Sebastian Krieter
 */
public class SolutionGenerator extends AbstractAnalysis<List<LiteralSet>> {

	private final int max;

	public SolutionGenerator(ISatSolver solver, int max) {
		super(solver);
		this.max = max;
	}

	public SolutionGenerator(CNF satInstance, int max) {
		super(satInstance);
		this.max = max;
	}

	@Override
	public List<LiteralSet> analyze(IMonitor monitor) throws Exception {
		final ArrayList<LiteralSet> solutionList = new ArrayList<>();
		solver.setGlobalTimeout(true);
		SatResult hasSolution = solver.hasSolution();
		while ((max > solutionList.size()) && (hasSolution == SatResult.TRUE)) {
			final int[] solution = solver.getSolution();
			solutionList.add(new LiteralSet(solution));
			try {
				solver.addClause(new LiteralSet(solution).negate());
			} catch (final RuntimeContradictionException e) {
				break;
			}
			hasSolution = solver.hasSolution();
		}
		return solutionList;
	}

}
