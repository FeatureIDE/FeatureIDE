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
import java.util.HashSet;
import java.util.List;
import java.util.Random;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.mig.MIGBuilder;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationUtil {

	protected static final int GLOBAL_SOLUTION_LIMIT = 100_000;

	public static long seed = 123456789;

	protected final List<TWiseConfiguration> incompleteSolutionList;
	protected final Solution[] solverSolutions = new Solution[GLOBAL_SOLUTION_LIMIT];
	protected final HashSet<Solution> solutionSet = new HashSet<>();
	protected final Random rnd = new Random(seed);

	protected final CNF cnf;
	protected final ISatSolver localSolver;

	protected ModalImplicationGraph mig;

	public TWiseConfigurationUtil(CNF cnf, ISatSolver localSolver, List<TWiseConfiguration> incompleteSolutionList) {
		this.cnf = cnf;
		this.localSolver = localSolver;
		this.incompleteSolutionList = incompleteSolutionList;
	}

	public void computeMIG() {
		if (ITWiseConfigurationGenerator.VERBOSE) {
			System.out.print("Init graph... ");
		}
		mig = LongRunningWrapper.runMethod(new MIGBuilder(localSolver.getSatInstance(), false));
		if (ITWiseConfigurationGenerator.VERBOSE) {
			System.out.println("Done!");
		}
	}

	public List<List<ClauseList>> removeCoreDeadFeatures(List<List<ClauseList>> expressions) {
		final LiteralSet coreDeadFeature = getDeadCoreFeatures();

		final List<List<ClauseList>> newGroupList = new ArrayList<>(expressions.size());
		for (final List<ClauseList> group : expressions) {
			if (!coreDeadFeature.isEmpty()) {
				final List<ClauseList> newNodeList = new ArrayList<>();
				expressionLoop: for (final List<LiteralSet> clauses : group) {
					final List<LiteralSet> variableClauses = new ArrayList<>();
					for (final LiteralSet clause : clauses) {
						// If clause can be satisfied
						if ((clause.countConflicts(coreDeadFeature) == 0)) {
							// If clause is already satisfied
							if (coreDeadFeature.containsAll(clause)) {
								continue expressionLoop;
							} else {
								variableClauses.add(clause);
							}
						}
					}
					if (!variableClauses.isEmpty()) {
						newNodeList.add(new ClauseList(variableClauses));
					}
				}
				newGroupList.add(newNodeList);
			} else {
				newGroupList.add(group);
			}
		}
		return newGroupList;
	}

	private LiteralSet getDeadCoreFeatures() {
		final int[] coreDead = new int[localSolver.getSatInstance().getVariables().size()];
		int index = 0;
		for (final Vertex vertex : mig.getAdjList()) {
			if (vertex.isCore()) {
				coreDead[index++] = vertex.getVar();
			}
		}
		final LiteralSet coreDeadFeature = new LiteralSet(Arrays.copyOf(coreDead, index));
		if (!coreDeadFeature.isEmpty()) {
			localSolver.assignmentPushAll(coreDeadFeature.getLiterals());
		}
		return coreDeadFeature;
	}

	public CNF getCnf() {
		return cnf;
	}

	public ISatSolver getSolver() {
		return localSolver;
	}

	public ModalImplicationGraph getMig() {
		return mig;
	}

	public boolean hasSolver() {
		return localSolver != null;
	}

	public Random getRandom() {
		return rnd;
	}

	protected int solverSolutionEndIndex = -1;

	public void addSolverSolution(int[] literals) {
		final Solution solution = new Solution(literals);
		if (solutionSet.add(solution)) {
			solverSolutionEndIndex++;
			solverSolutionEndIndex %= GLOBAL_SOLUTION_LIMIT;
			final Solution oldSolution = solverSolutions[solverSolutionEndIndex];
			if (oldSolution != null) {
				solutionSet.remove(oldSolution);
			}
			solverSolutions[solverSolutionEndIndex] = solution;

			for (final TWiseConfiguration configuration : incompleteSolutionList) {
				configuration.updateSolverSolutions(literals, solverSolutionEndIndex);
			}
		}
	}

	public Solution getSolverSolution(int index) {
		return solverSolutions[index];
	}

	public Solution[] getSolverSolutions() {
		return solverSolutions;
	}

}
