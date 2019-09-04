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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator.Deduce;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.UniformRandomConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.mig.CollectingVisitor;
import de.ovgu.featureide.fm.core.analysis.mig.MIGBuilder;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.mig.Traverser;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
class TWiseConfigurationUtil {

	public static final int GLOBAL_SOLUTION_LIMIT = 100_000;

	final static Comparator<Pair<LiteralSet, TWiseConfiguration>> candidateLengthComparator = new CandidateLengthComparator();

	protected final LiteralSet[] solverSolutions = new LiteralSet[GLOBAL_SOLUTION_LIMIT];
	protected final HashSet<LiteralSet> solutionSet = new HashSet<>();
	protected Random random = new Random(42);

	protected final List<LiteralSet> randomSample;

	private final List<TWiseConfiguration> incompleteSolutionList = new LinkedList<>();
	private final List<TWiseConfiguration> completeSolutionList = new ArrayList<>();

	protected final CNF cnf;
	protected final int t;
	protected final ISatSolver localSolver;

	protected ModalImplicationGraph mig;
	protected LiteralSet[] strongHull;

	protected int maxSampleSize = Integer.MAX_VALUE;

	public TWiseConfigurationUtil(CNF cnf, int t, ISatSolver localSolver) {
		this.cnf = cnf;
		this.t = t;
		this.localSolver = localSolver;

		final UniformRandomConfigurationGenerator randomGenerator = new UniformRandomConfigurationGenerator(cnf, 10000);
		randomGenerator.setAllowDuplicates(false);
		randomGenerator.setSampleSize(1000);
		randomGenerator.setRandom(random);
		randomSample = LongRunningWrapper.runMethod(randomGenerator);

		for (final LiteralSet solution : randomSample) {
			addSolverSolution(solution.getLiterals());
		}
	}

	public void computeMIG() {
		if (ITWiseConfigurationGenerator.VERBOSE) {
			System.out.print("Init graph... ");
		}
		mig = LongRunningWrapper.runMethod(new MIGBuilder(localSolver.getSatInstance(), false));
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
		if (ITWiseConfigurationGenerator.VERBOSE) {
			System.out.println("Done!");
		}
	}

	public LiteralSet getDeadCoreFeatures() {
		if (localSolver == null) {
			return new LiteralSet();
		}
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

	public int getT() {
		return t;
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
		return random;
	}

	protected int solverSolutionEndIndex = -1;

	public void addSolverSolution(int[] literals) {
		final LiteralSet solution = new LiteralSet(literals, Order.INDEX, false);
		if (solutionSet.add(solution)) {
			solverSolutionEndIndex++;
			solverSolutionEndIndex %= GLOBAL_SOLUTION_LIMIT;
			final LiteralSet oldSolution = solverSolutions[solverSolutionEndIndex];
			if (oldSolution != null) {
				solutionSet.remove(oldSolution);
			}
			solverSolutions[solverSolutionEndIndex] = solution;

			for (final TWiseConfiguration configuration : getIncompleteSolutionList()) {
				configuration.updateSolverSolutions(literals, solverSolutionEndIndex);
			}
		}
	}

	public LiteralSet getSolverSolution(int index) {
		return solverSolutions[index];
	}

	public LiteralSet[] getSolverSolutions() {
		return solverSolutions;
	}

	public boolean isCombinationValid(LiteralSet literals) {
		return !isCombinationInvalidMIG(literals) && isCombinationValidSAT(literals);
	}

	public boolean isCombinationValid(ClauseList clauses) {
		if (hasSolver()) {
			for (final LiteralSet literalSet : clauses) {
				if (isCombinationInvalidMIG(literalSet)) {
					return false;
				}
			}
			for (final LiteralSet literalSet : clauses) {
				if (isCombinationValidSAT(literalSet)) {
					return true;
				}
			}
			return false;
		}
		return !clauses.isEmpty();
	}

	public boolean isCombinationInvalidMIG(LiteralSet literals) {
		if (hasSolver()) {
			for (final int literal : literals.getLiterals()) {
				if (strongHull[mig.getVertex(literal).getId()].hasConflicts(literals)) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean isCombinationValidSAT(LiteralSet literals) {
		if (hasSolver()) {
			for (final LiteralSet s : randomSample) {
				if (!s.hasConflicts(literals)) {
					return true;
				}
			}

			final ISatSolver solver = getSolver();
			final int orgAssingmentLength = solver.getAssignmentSize();
			solver.assignmentPushAll(literals.getLiterals());
			try {
				final SatResult hasSolution = solver.hasSolution();
				switch (hasSolution) {
				case TRUE:
					addSolverSolution(solver.getSolution());
					break;
				case FALSE:
				case TIMEOUT:
					return false;
				default:
					break;
				}
			} finally {
				solver.assignmentClear(orgAssingmentLength);
			}
		}
		return true;
	}

	public boolean removeInvalidClauses(ClauseList nextCondition, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		int validCount = nextCondition.size();
		for (final LiteralSet literals : nextCondition) {
			if (!isCombinationValid(literals)) {
				validCount--;
				for (final Iterator<Pair<LiteralSet, TWiseConfiguration>> iterator = candidatesList.iterator(); iterator.hasNext();) {
					final Pair<LiteralSet, TWiseConfiguration> pair = iterator.next();
					if (pair.getKey().equals(literals)) {
						iterator.remove();
					}
				}
			}
		}
		return validCount == 0;
	}

	public boolean isSelectionPossible(final LiteralSet literals, final TWiseConfiguration configuration, boolean useSolver) {
		if (hasSolver()) {
			if (useSolver) {
				final ISatSolver localSolver = getSolver();
				final int orgAssignmentSize = configuration.setUpSolver(localSolver);
				try {
					final int[] configurationLiterals = configuration.getLiterals();
					for (final int literal : literals.getLiterals()) {
						if (configurationLiterals[Math.abs(literal) - 1] == 0) {
							localSolver.assignmentPush(literal);
						}
					}
					if (orgAssignmentSize < localSolver.getAssignmentSize()) {
						if (localSolver.hasSolution() != SatResult.TRUE) {
							return false;
						}
					}
				} finally {
					localSolver.assignmentClear(orgAssignmentSize);
				}
			} else {
				final VecInt solverSolutionIndex = configuration.getSolverSolutionIndex();
				for (int i = 0; i < solverSolutionIndex.size(); i++) {
					if (!getSolverSolution(solverSolutionIndex.get(i)).hasConflicts(literals)) {
						return true;
					}
				}
				return false;
			}
		}
		return true;
	}

	public static boolean isCovered(ClauseList condition, Iterable<? extends LiteralSet> solutionList) {
		for (final LiteralSet configuration : solutionList) {
			for (final LiteralSet literals : condition) {
				if (configuration.containsAll(literals)) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean isCovered(ClauseList condition) {
		return isCovered(condition, completeSolutionList) || isCovered(condition, incompleteSolutionList);
	}

	public boolean select(TWiseConfiguration solution, Deduce deduce, LiteralSet literals) {
		selectLiterals(solution, deduce, literals);

		if (solution.isComplete()) {
			solution.clear();
			for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
				if (iterator.next() == solution) {
					iterator.remove();
					completeSolutionList.add(solution);
					break;
				}
			}
			return true;
		} else {
			return false;
		}
	}

	private void selectLiterals(TWiseConfiguration solution, Deduce deduce, LiteralSet literals) {
		solution.setLiteral(literals.getLiterals());
		if (hasSolver()) {
			switch (deduce) {
			case AC:
				solution.autoComplete();
				break;
			case DP:
				solution.propagation();
				break;
			case NONE:
				break;
			}
		}
	}

	public boolean isCandidate(final LiteralSet literals, TWiseConfiguration solution) {
		return !solution.hasConflicts(literals);
	}

	public void addCandidates(final LiteralSet literals, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		for (final TWiseConfiguration configuration : getIncompleteSolutionList()) {
			if (isCandidate(literals, configuration)) {
				candidatesList.add(new Pair<>(literals, configuration));
			}
		}
	}

	public void initCandidatesList(ClauseList nextCondition, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		candidatesList.clear();
		for (final LiteralSet literals : nextCondition) {
			addCandidates(literals, candidatesList);
		}
		Collections.sort(candidatesList, candidateLengthComparator);
	}

	protected boolean cover(boolean useSolver, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossible(pair.getKey(), pair.getValue(), useSolver)) {
				select(pair.getValue(), Deduce.NONE, pair.getKey());
				return true;
			}
		}
		return false;
	}

	public void newConfiguration(final LiteralSet literals) {
		if (completeSolutionList.size() < maxSampleSize) {
			final TWiseConfiguration configuration = new TWiseConfiguration(this);
			selectLiterals(configuration, Deduce.DP, literals);
			configuration.updateSolverSolutions();
			if (configuration.isComplete()) {
				configuration.clear();
				completeSolutionList.add(configuration);
			} else {
				incompleteSolutionList.add(configuration);
//				Collections.sort(incompleteSolutionList, configurationLengthComparator);
			}
		}
	}

	public List<TWiseConfiguration> getIncompleteSolutionList() {
		return incompleteSolutionList;
	}

	public List<TWiseConfiguration> getCompleteSolutionList() {
		return completeSolutionList;
	}

	public List<TWiseConfiguration> getResultList() {
		final ArrayList<TWiseConfiguration> resultList = new ArrayList<>(completeSolutionList.size() + incompleteSolutionList.size());
		resultList.addAll(incompleteSolutionList);
		resultList.addAll(completeSolutionList);
		return resultList;
	}

	public int getMaxSampleSize() {
		return maxSampleSize;
	}

	public void setMaxSampleSize(int maxSampleSize) {
		this.maxSampleSize = maxSampleSize;
	}

	public void setRandom(Random random) {
		this.random = random;
	}

}
