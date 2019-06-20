/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.ICombinationIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.LexicographicIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceCondition;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise.PresenceConditionManager;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.mig.CollectingVisitor;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.mig.Traverser;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;

/**
 * Test whether a set of configurations achieves t-wise feature coverage.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationTester {

	private final int t;
	private final CNF cnf;
	private final PresenceConditionManager presenceConditionManager;
	private final ISatSolver solver;
	private final ModalImplicationGraph mig;
	private final List<Solution> configurations;

	protected LiteralSet[] strongHull;

	public TWiseConfigurationTester(CNF cnf, int t, List<List<ClauseList>> nodeArray, List<Solution> configurations) {
		this.cnf = cnf;
		this.t = t;
		this.configurations = configurations;
		if (!this.cnf.getClauses().isEmpty()) {
			solver = new AdvancedSatSolver(this.cnf);
			final TWiseConfigurationUtil util = new TWiseConfigurationUtil(cnf, solver);
			util.computeMIG();
			presenceConditionManager = new PresenceConditionManager(util, nodeArray);
			mig = util.getMig();
			genHulls();
		} else {
			solver = null;
			mig = null;
			presenceConditionManager = new PresenceConditionManager(new TWiseConfigurationUtil(cnf, null), nodeArray);
		}
	}

	private void genHulls() {
		strongHull = new LiteralSet[mig.getAdjList().size()];

		for (final Vertex vertex : mig.getAdjList()) {
			final int literalSet = vertex.getVar();
			final Traverser traverser = new Traverser(mig);
			traverser.setModel(new int[mig.getAdjList().size()]);
			final CollectingVisitor visitor = new CollectingVisitor();
			traverser.setVisitor(visitor);
			traverser.traverse(literalSet);
			final VecInt strong = visitor.getResult()[0];
			strongHull[vertex.getId()] = new LiteralSet(Arrays.copyOf(strong.toArray(), strong.size()));
		}
	}

	public boolean test() {
		return (testSolutionValidity() == null) && (testCompleteness() == null);
	}

	public PresenceCondition[] testCompleteness() throws AssertionError {
		final TWiseCombiner combiner = new TWiseCombiner(cnf.getVariables().size());
		final ClauseList combinations = new ClauseList();

		for (final List<PresenceCondition> expressions : presenceConditionManager.getGroupedPresenceConditions()) {
			comboLoop: for (final ICombinationIterator iterator = new LexicographicIterator(t, expressions); iterator.hasNext();) {
				final PresenceCondition[] clauseListArray = iterator.next();
				if (clauseListArray == null) {
					break;
				}

				if (isCovered(clauseListArray)) {
					continue comboLoop;
				}

				combinations.clear();
				combiner.combineConditions(clauseListArray, combinations);

				if (solver != null) {
					for (final Iterator<LiteralSet> it = combinations.iterator(); it.hasNext();) {
						if (checkMig(it.next())) {
							it.remove();
						}
					}

					for (final Iterator<LiteralSet> it = combinations.iterator(); it.hasNext();) {
						if (checkSolver(it.next())) {
							it.remove();
						} else {
							break;
						}
					}
				}

				if (combinations.isEmpty()) {
					continue comboLoop;
				}

				return clauseListArray;
			}
		}
		return null;
	}

	private boolean checkSolver(final LiteralSet literalSet) throws AssertionError {
		for (final Integer literal : literalSet.getLiterals()) {
			solver.assignmentPush(literal);
		}
		final SatResult hasSolution = solver.hasSolution();
		switch (hasSolution) {
		case FALSE:
			solver.assignmentClear(0);
			return true;
		case TIMEOUT:
			System.err.println("Timeout!");
			solver.assignmentClear(0);
			return true;
		case TRUE:
			solver.assignmentClear(0);
			return false;
		default:
			throw new AssertionError();
		}
	}

	private boolean checkMig(final LiteralSet literalSet) {
		for (final int literal : literalSet.getLiterals()) {
			if (strongHull[mig.getVertex(literal).getId()].hasConflicts(literalSet)) {
				return true;
			}
		}
		return false;
	}

	private boolean isCovered(final PresenceCondition[] clauseListArray) {
		configurationLoop: for (final Solution solution : configurations) {
			for (final PresenceCondition condition : clauseListArray) {
				if (!containsAtLeastOne(solution, condition.getClauses())) {
					continue configurationLoop;
				}
			}
			return true;
		}
		return false;
	}

	public Solution testSolutionValidity() throws AssertionError {
		if (solver != null) {
			final int c = 0;
			for (final Solution is : configurations) {
				final SatResult hasSolution = solver.hasSolution(is.getLiterals());
				switch (hasSolution) {
				case FALSE:
					return is;
				case TIMEOUT:
					System.err.println("Timeout! " + c);
					break;
				case TRUE:
					break;
				default:
					throw new AssertionError();
				}
			}
		}
		return null;
	}

	private boolean containsAtLeastOne(final Solution solution, final ClauseList clauseList) {
		for (final LiteralSet literalSet : clauseList) {
			if (solution.containsAll(literalSet)) {
				return true;
			}
		}
		return false;
	}

}
