/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2023  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ModifiableSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds core and dead features.
 *
 * @author Sebastian Krieter
 */
public class PrimeImplicantsAnalysis extends AVariableAnalysis<List<LiteralSet>> {

	public PrimeImplicantsAnalysis(ISatSolver solver) {
		this(solver, null);
	}

	public PrimeImplicantsAnalysis(CNF satInstance) {
		this(satInstance, null);
	}

	public PrimeImplicantsAnalysis(CNF satInstance, LiteralSet variables) {
		super(satInstance);
		this.variables = variables;
	}

	public PrimeImplicantsAnalysis(ISatSolver solver, LiteralSet variables) {
		super(solver);
		this.variables = variables;
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
		final List<LiteralSet> primeImplicants = new ArrayList<>();
		while (true) {
			monitor.checkCancel();
			final int[] solution = solver.getPrimeImplicant();
			if (solution != null) {
				final LiteralSet primeImplicant = new LiteralSet(solution);
				primeImplicants.add(primeImplicant);
				solver.addClause(primeImplicant.negate());
			} else {
				break;
			}
		}
		return primeImplicants;
	}

}
