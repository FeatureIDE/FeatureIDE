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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.ICombinationIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.LexicographicIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.mig.CollectingVisitor;
import de.ovgu.featureide.fm.core.analysis.mig.MIGBuilder;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.mig.Traverser;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Test whether a set of configurations achieves t-wise feature coverage.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationTester {

	private final int t;
	private final CNF cnf;
	private final List<List<ClauseList>> nodeArray;
	private final ISatSolver solver;
	private final ModalImplicationGraph mig;
	private final List<Solution> configurations;

	protected LiteralSet[] strongHull;

	public TWiseConfigurationTester(CNF cnf, int t, List<List<ClauseList>> nodeArray, List<Solution> configurations) {
		this.cnf = cnf;
		this.t = t;
		this.nodeArray = nodeArray;
		this.configurations = configurations;
		if (!this.cnf.getClauses().isEmpty()) {
			solver = new AdvancedSatSolver(this.cnf);
			mig = LongRunningWrapper.runMethod(new MIGBuilder(solver.getSatInstance(), false));
			genHulls();
		} else {
			solver = null;
			mig = null;
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
		return testSolutionValidity() && testCompleteness();
	}

	public boolean testCompleteness() throws AssertionError {
		final int[] clauseIndex = new int[t];
		final ArrayList<LiteralSet> combinations = new ArrayList<>();

		System.out.print("\tTesting combination completeness...");
		for (final List<ClauseList> expressions : nodeArray) {
			comboLoop: for (final ICombinationIterator iterator = new LexicographicIterator(t, expressions); iterator.hasNext();) {
				final ClauseList[] clauseListArray = iterator.next();
				if (clauseListArray == null) {
					break;
				}

				if (isCovered(clauseListArray)) {
					continue comboLoop;
				}

				Arrays.fill(clauseIndex, 0);
				clauseIndex[0] = -1;
				combinations.clear();

				int i = 0;
				loop: while (i < t) {
					for (i = 0; i < t; i++) {
						final int cindex = clauseIndex[i];
						if (cindex == (clauseListArray[i].size() - 1)) {
							clauseIndex[i] = 0;
						} else {
							clauseIndex[i] = cindex + 1;

							final LiteralSet literalSet = getCombinationLiterals(clauseIndex, clauseListArray);
							if (literalSet != null) {
								combinations.add(literalSet);
								continue loop;
							}
						}
					}
				}

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

				System.out.println(" FAIL");
				System.out.println("\tUncovered combination. " + iterator.getIndex() + " - " + Arrays.toString(clauseListArray));
				return false;
			}
		}
		System.out.println(" PASS");
		return true;
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

	private LiteralSet getCombinationLiterals(final int[] clauseIndex, final ClauseList[] clauseListArray) {
		final TreeSet<Integer> newLiteralSet = new TreeSet<>();
		for (int j = 0; j < t; j++) {
			for (final int literal : clauseListArray[j].get(clauseIndex[j]).getLiterals()) {
				if (newLiteralSet.contains(-literal)) {
					return null;
				} else {
					newLiteralSet.add(literal);
				}
			}
		}

		final int[] combinationLiterals = new int[newLiteralSet.size()];
		int j = 0;
		for (final Integer literal : newLiteralSet) {
			combinationLiterals[j++] = literal;
		}
		final LiteralSet literalSet = new LiteralSet(combinationLiterals);
		return literalSet;
	}

	private boolean isCovered(final ClauseList[] clauseListArray) {
		configurationLoop: for (final Solution solution : configurations) {
			for (final ClauseList clauseList : clauseListArray) {
				if (!containsAtLeastOne(solution, clauseList)) {
					continue configurationLoop;
				}
			}
			return true;
		}
		return false;
	}

	public boolean testSolutionValidity() throws AssertionError {
		System.out.println("Testing results...");
		if (solver != null) {
			System.out.print("\tTesting configuration validity...");
			final int c = 0;
			for (final Solution is : configurations) {
				final SatResult hasSolution = solver.hasSolution(is.getLiterals());
				switch (hasSolution) {
				case FALSE:
					System.out.println(" FAIL");
					System.out.println("\tInvalid configuration: " + is);
					return false;
				case TIMEOUT:
					System.err.println("Timeout! " + c);
					break;
				case TRUE:
					break;
				default:
					throw new AssertionError();
				}
			}
			System.out.println(" PASS");
			return true;
		}
		System.out.println(" SKIPPED");
		return false;
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
