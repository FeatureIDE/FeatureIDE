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

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Random;
import java.util.concurrent.Semaphore;
import java.util.stream.Stream;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator.Deduce;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.RandomConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.mig.MIGBuilder;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;
import de.ovgu.featureide.fm.core.io.ModalImplicationGraphFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.ConsoleMonitor;

/**
 * Contains several intermediate results and functions for generating a t-wise sample.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationUtil {

	private class SolverPool {

		private final LinkedList<ISatSolver> available = new LinkedList<>();
		private final HashMap<ISatSolver, ISatSolver> used = new HashMap<>();
		private final Semaphore s;

		private final int assignmentSize;

		public SolverPool(int size, ISatSolver template) {
			s = new Semaphore(size);
			assignmentSize = template.getAssignmentSize();
			for (int i = 0; i < size; i++) {
				final ISatSolver solver = new AdvancedSatSolver(template.getSatInstance());
				solver.assignmentPushAll(template.getAssignmentArray());
				solver.useSolutionList(0);
				solver.setSelectionStrategy(SelectionStrategy.ORG);
				available.add(solver);
			}
		}

		public ISatSolver acquire() {
			try {
				s.acquire();
				synchronized (this) {
					final ISatSolver solver = available.removeFirst();
					used.put(solver, solver);
					return solver;
				}
			} catch (final InterruptedException e) {
				return null;
			}
		}

		public void release(ISatSolver solver) {
			synchronized (this) {
				final ISatSolver freedSolver = used.remove(solver);
				freedSolver.assignmentClear(assignmentSize);
				available.addLast(freedSolver);
			}
			s.release();
		}

	}

	public static final int GLOBAL_SOLUTION_LIMIT = 100_000;

	final static Comparator<Pair<LiteralSet, TWiseConfiguration>> candidateLengthComparator = new CandidateLengthComparator();

	protected final LiteralSet[] solverSolutions = new LiteralSet[GLOBAL_SOLUTION_LIMIT];
	protected final HashSet<LiteralSet> solutionSet = new HashSet<>();
	protected Random random = new Random(42);

	protected List<LiteralSet> randomSample;

	private final List<TWiseConfiguration> incompleteSolutionList = new LinkedList<>();
	private final List<TWiseConfiguration> completeSolutionList = new ArrayList<>();

	protected final CNF cnf;
	protected final ISatSolver localSolver;
	protected final boolean hasSolver;
	protected SolverPool localSolverPool;

	protected ModalImplicationGraph mig;
	protected LiteralSet[] strongHull;
	protected LiteralSet coreDead;

	protected int maxSampleSize = Integer.MAX_VALUE;

	private Deduce createConfigurationDeduce = Deduce.DP;
	private Deduce extendConfigurationDeduce = Deduce.NONE;

	public TWiseConfigurationUtil(CNF cnf, ISatSolver localSolver) {
		this.cnf = cnf;
		this.localSolver = localSolver;
		hasSolver = localSolver != null;

		randomSample = Collections.emptyList();
	}

	public void computeRandomSample(int randomSampleSize) {
		final RandomConfigurationGenerator randomGenerator = new RandomConfigurationGenerator(cnf, randomSampleSize);
		randomGenerator.setAllowDuplicates(true);
		randomGenerator.setRandom(random);
		randomSample = LongRunningWrapper.runMethod(randomGenerator);

		for (final LiteralSet solution : randomSample) {
			addSolverSolution(solution.getLiterals());
		}
	}

	public void computeMIG(boolean migCheckRedundancy, boolean migDetectStrong) {
		if (TWiseConfigurationGenerator.VERBOSE) {
			System.out.println("Init graph... ");
			System.out.println("\tCompute graph... ");
		}
		final MIGBuilder migBuilder = new MIGBuilder(cnf);
		migBuilder.setCheckRedundancy(migCheckRedundancy);
		migBuilder.setDetectStrong(migDetectStrong);
		mig = LongRunningWrapper.runMethod(migBuilder, new ConsoleMonitor<>());
		strongHull = new LiteralSet[mig.getAdjList().size()];

		for (final Vertex vertex : mig.getAdjList()) {
			final int[] strongEdges = vertex.getStrongEdges();
			strongHull[vertex.getId()] = new LiteralSet(Arrays.copyOf(strongEdges, strongEdges.length));
		}
	}

	public void computeMIG(Path migPath) {
		if (TWiseConfigurationGenerator.VERBOSE) {
			System.out.println("Init graph... ");
			System.out.println("\tLoad graph from " + migPath);
		}
		mig = new ModalImplicationGraph();
		FileHandler.load(migPath, mig, new ModalImplicationGraphFormat());
		strongHull = new LiteralSet[mig.getAdjList().size()];

		for (final Vertex vertex : mig.getAdjList()) {
			final int[] strongEdges = vertex.getStrongEdges();
			strongHull[vertex.getId()] = new LiteralSet(Arrays.copyOf(strongEdges, strongEdges.length));
		}
	}

	public LiteralSet getDeadCoreFeatures() {
		if (coreDead == null) {
			if (hasMig()) {
				computeDeadCoreFeaturesMig();
			} else {
				computeDeadCoreFeatures();
			}
			localSolverPool = new SolverPool(16, localSolver);
		}
		return coreDead;
	}

	public LiteralSet computeDeadCoreFeaturesMig() {
		if (hasSolver()) {
			coreDead = new LiteralSet();
		} else {
			final int[] coreDeadArray = new int[cnf.getVariables().size()];
			int index = 0;
			for (final Vertex vertex : mig.getAdjList()) {
				if (vertex.isCore()) {
					coreDeadArray[index++] = vertex.getVar();
				}
			}
			coreDead = new LiteralSet(Arrays.copyOf(coreDeadArray, index));
			if (!coreDead.isEmpty()) {
				localSolver.assignmentPushAll(coreDead.getLiterals());
			}
		}
		return coreDead;
	}

	public LiteralSet computeDeadCoreFeatures() {
		final AdvancedSatSolver solver = new AdvancedSatSolver(cnf);
		final int[] firstSolution = solver.findSolution();
		if (firstSolution != null) {
			final int[] coreDeadArray = new int[firstSolution.length];
			int coreDeadIndex = 0;
			solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
			LiteralSet.resetConflicts(firstSolution, solver.findSolution());
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

			// find core/dead features
			for (int i = 0; i < firstSolution.length; i++) {
				final int varX = firstSolution[i];
				if (varX != 0) {
					solver.assignmentPush(-varX);
					switch (solver.hasSolution()) {
					case FALSE:
						solver.assignmentReplaceLast(varX);
						coreDeadArray[coreDeadIndex++] = varX;
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						LiteralSet.resetConflicts(firstSolution, solver.getSolution());
						solver.shuffleOrder(random);
						break;
					}
				}
			}
			coreDead = new LiteralSet(Arrays.copyOf(coreDeadArray, coreDeadIndex));
			if (!coreDead.isEmpty()) {
				localSolver.assignmentPushAll(coreDead.getLiterals());
			}
		} else {
			coreDead = new LiteralSet();
		}
		return coreDead;
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
		return hasSolver;
	}

	public boolean hasMig() {
		return mig != null;
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
			if (hasMig()) {
				for (final LiteralSet literalSet : clauses) {
					if (isCombinationInvalidMIG(literalSet)) {
						return false;
					}
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
		if (hasMig()) {
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

//			final ISatSolver solver = localSolverPool.acquire();
			final ISatSolver solver = getSolver();
			final int orgAssingmentLength = solver.getAssignmentSize();
			try {
				solver.assignmentPushAll(literals.getLiterals());
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
//				localSolverPool.release(solver);
				solver.assignmentClear(orgAssingmentLength);
			}
		}
		return true;
	}

	public boolean removeInvalidClauses(ClauseList nextCondition, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		final LinkedList<LiteralSet> invalidClauses = new LinkedList<>();
		for (final Iterator<LiteralSet> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralSet literals = conditionIterator.next();
			if (!isCombinationValid(literals)) {
				invalidClauses.add(literals);
				conditionIterator.remove();
			}
		}
		if (nextCondition.isEmpty()) {
			candidatesList.clear();
			return true;
		} else {
			removeInvalidCandidates(candidatesList, invalidClauses);
			return false;
		}
	}

	public boolean removeInvalidClausesSat(ClauseList nextCondition, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		final LinkedList<LiteralSet> invalidClauses = new LinkedList<>();
		for (final Iterator<LiteralSet> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralSet literals = conditionIterator.next();
			if (!isCombinationValidSAT(literals)) {
				invalidClauses.add(literals);
				conditionIterator.remove();
			}
		}
		if (nextCondition.isEmpty()) {
			candidatesList.clear();
			return true;
		} else {
			removeInvalidCandidates(candidatesList, invalidClauses);
			return false;
		}
	}

	public boolean removeInvalidClausesLight(ClauseList nextCondition, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		final LinkedList<LiteralSet> invalidClauses = new LinkedList<>();
		for (final Iterator<LiteralSet> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralSet literals = conditionIterator.next();
			if (isCombinationInvalidMIG(literals)) {
				invalidClauses.add(literals);
				conditionIterator.remove();
			}
		}
		if (nextCondition.isEmpty()) {
			candidatesList.clear();
			return true;
		} else {
			removeInvalidCandidates(candidatesList, invalidClauses);
			return false;
		}
	}

	private void removeInvalidCandidates(List<Pair<LiteralSet, TWiseConfiguration>> candidatesList, final LinkedList<LiteralSet> invalidClauses) {
		for (final LiteralSet literals : invalidClauses) {
			for (final Iterator<Pair<LiteralSet, TWiseConfiguration>> candidateIterator = candidatesList.iterator(); candidateIterator.hasNext();) {
				final Pair<LiteralSet, TWiseConfiguration> pair = candidateIterator.next();
				if (pair.getKey().equals(literals)) {
					candidateIterator.remove();
				}
			}
		}
	}

	public boolean removeInvalidClausesLight(ClauseList nextCondition) {
		for (final Iterator<LiteralSet> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralSet literals = conditionIterator.next();
			if (isCombinationInvalidMIG(literals)) {
				conditionIterator.remove();
			}
		}
		return nextCondition.isEmpty();
	}

	private boolean isSelectionPossibleSol(Pair<LiteralSet, TWiseConfiguration> candidate) {
		final VecInt solverSolutionIndex = candidate.getValue().getSolverSolutionIndex();
		for (int i = 0; i < solverSolutionIndex.size(); i++) {
			if (!getSolverSolution(solverSolutionIndex.get(i)).hasConflicts(candidate.getKey())) {
				return true;
			}
		}
		return false;
	}

	private boolean isSelectionPossibleSol(LiteralSet literals, TWiseConfiguration configuration) {
		final VecInt solverSolutionIndex = configuration.getSolverSolutionIndex();
		for (int i = 0; i < solverSolutionIndex.size(); i++) {
			if (!getSolverSolution(solverSolutionIndex.get(i)).hasConflicts(literals)) {
				return true;
			}
		}
		return false;
	}

	private boolean isSelectionPossibleSat(final LiteralSet literals, final TWiseConfiguration configuration) {
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
		return true;
	}

	private boolean isSelectionPossibleSatPara(final LiteralSet literals, final TWiseConfiguration configuration) {
		final ISatSolver localSolver = localSolverPool.acquire();
		try {
			final int orgAssignmentSize = configuration.setUpSolver(localSolver);
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
			localSolverPool.release(localSolver);
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

	private Stream<TWiseConfiguration> getConfigurationStream() {
		return Stream.concat(getCompleteSolutionList().parallelStream(), getIncompleteSolutionList().parallelStream());
	}

	public boolean isCoveredPara(ClauseList condition) {
		final Optional<TWiseConfiguration> coveringSolution = condition.stream() //
				.flatMap(literals -> getConfigurationStream() //
						.filter(configuration -> configuration.containsAll(literals)))//
				.findAny();
		return coveringSolution.isPresent();
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

	public boolean isCandidate(final Pair<LiteralSet, TWiseConfiguration> pair) {
		return !pair.getValue().hasConflicts(pair.getKey());
	}

	public void addCandidates(final LiteralSet literals, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		for (final TWiseConfiguration configuration : getIncompleteSolutionList()) {
			if (isCandidate(literals, configuration)) {
				candidatesList.add(new Pair<>(literals, configuration));
			}
		}
	}

	public void initCandidatesListPara(ClauseList nextCondition, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		candidatesList.clear();
		nextCondition.stream() //
				.flatMap(literals -> getIncompleteSolutionList().parallelStream() //
						.filter(configuration -> isCandidate(literals, configuration)) //
						.map(configuration -> new Pair<>(literals, configuration)))//
				.sorted(candidateLengthComparator) //
				.forEach(candidatesList::add);
	}

	public void initCandidatesList(ClauseList nextCondition, List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		candidatesList.clear();
		for (final LiteralSet literals : nextCondition) {
			for (final TWiseConfiguration configuration : getIncompleteSolutionList()) {
				if (isCandidate(literals, configuration)) {
					candidatesList.add(new Pair<>(literals, configuration));
				}
			}
		}
		Collections.sort(candidatesList, candidateLengthComparator);
	}

	protected boolean coverSol(List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossibleSol(pair.getKey(), pair.getValue())) {
				select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
				assert pair.getValue().isValid();
				return true;
			}
		}
		return false;
	}

	protected boolean coverSat(List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossibleSat(pair.getKey(), pair.getValue())) {
				select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
				assert pair.getValue().isValid();
				return true;
			}
		}
		return false;
	}

	protected boolean coverSolPara(List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		final Optional<Pair<LiteralSet, TWiseConfiguration>> candidate = candidatesList.parallelStream() //
				.filter(this::isSelectionPossibleSol) //
				.findFirst();

		if (candidate.isPresent()) {
			final Pair<LiteralSet, TWiseConfiguration> pair = candidate.get();
			select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
			assert pair.getValue().isValid();
			return true;
		} else {
			return false;
		}
	}

	public boolean coverSatPara(List<Pair<LiteralSet, TWiseConfiguration>> candidatesList) {
		final Optional<Pair<LiteralSet, TWiseConfiguration>> findFirst =
			candidatesList.parallelStream().filter(pair -> isSelectionPossibleSatPara(pair.getKey(), pair.getValue())).findFirst();

		if (findFirst.isPresent()) {
			final Pair<LiteralSet, TWiseConfiguration> pair = findFirst.get();
			select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
			assert pair.getValue().isValid();
			return true;
		} else {
			return false;
		}
	}

	public void newConfiguration(final LiteralSet literals) {
		if (completeSolutionList.size() < maxSampleSize) {
			final TWiseConfiguration configuration = new TWiseConfiguration(this);
			selectLiterals(configuration, createConfigurationDeduce, literals);
			assert configuration.isValid();
			configuration.updateSolverSolutions();
			if (configuration.isComplete()) {
				configuration.clear();
				completeSolutionList.add(configuration);
			} else {
				incompleteSolutionList.add(configuration);
				Collections.sort(incompleteSolutionList, (a, b) -> a.countLiterals() - b.countLiterals());
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

	public void setCreateConfigurationDeduce(Deduce createConfigurationDeduce) {
		this.createConfigurationDeduce = createConfigurationDeduce;
	}

	public void setExtendConfigurationDeduce(Deduce extendConfigurationDeduce) {
		this.extendConfigurationDeduce = extendConfigurationDeduce;
	}

}
