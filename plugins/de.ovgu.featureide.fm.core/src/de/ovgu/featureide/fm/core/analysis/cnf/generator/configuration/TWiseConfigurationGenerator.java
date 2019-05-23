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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.IteratorFactory.IteratorID;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.MergeIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.CandidateLengthComparator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfiguration;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfigurationLengthComparator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfigurationUtil;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.MonitorThread;

/**
 * Generates configurations for a given propositional formula such that t-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationGenerator extends AConfigurationGenerator implements ITWiseConfigurationGenerator {

	/**
	 * Converts a set of single literals into a grouped expression list.
	 *
	 * @param literalSet the literal set
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertLiterals(LiteralSet literalSet) {
		return convertGroupedLiterals(Arrays.asList(literalSet));
	}

	/**
	 * Converts a grouped set of single literals into a grouped expression list.
	 *
	 * @param groupedLiterals the grouped literal sets
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertGroupedLiterals(List<LiteralSet> groupedLiterals) {
		final List<List<ClauseList>> groupedExpressions = new ArrayList<>(groupedLiterals.size());
		for (final LiteralSet literalSet : groupedLiterals) {
			final List<ClauseList> arrayList = new ArrayList<>(literalSet.size());
			groupedExpressions.add(arrayList);
			for (final Integer literal : literalSet.getLiterals()) {
				final ClauseList clauseList = new ClauseList(1);
				clauseList.add(new LiteralSet(literal));
				arrayList.add(clauseList);
			}
		}
		return groupedExpressions;
	}

	/**
	 * Converts an expression list into a grouped expression set with a single group.
	 *
	 * @param expressions the expression list
	 * @return a grouped expression list (can be used as an input for the configuration generator).
	 */
	public static List<List<ClauseList>> convertExpressions(List<ClauseList> expressions) {
		return Arrays.asList(expressions);
	}

	private static enum CombinationStatus {
		NOT_COVERED, COVERED, INVALID,
	}

	protected final static Comparator<TWiseConfiguration> configurationLengthComparator = new TWiseConfigurationLengthComparator();
	protected final static Comparator<Pair<LiteralSet, TWiseConfiguration>> candidateLengthComparator = new CandidateLengthComparator();

	protected final TWiseConfigurationUtil util;

	protected final List<Solution> randomSample;

	protected final List<TWiseConfiguration> incompleteSolutionList = new LinkedList<>();
	protected final List<TWiseConfiguration> completeSolutionList = new ArrayList<>();

	private final List<Pair<LiteralSet, TWiseConfiguration>> candidatesList = new ArrayList<>();
	private final Set<Pair<LiteralSet, TWiseConfiguration>> candidatesList2 = new HashSet<>();

	private int[] features;
	private final VecInt lits = new VecInt();

	protected final int t;
	protected List<List<ClauseList>> expressions;

	protected long numberOfCombinations, count, coveredCount, invalidCount, phaseCount;

	protected final MonitorThread samplingMonitor = new MonitorThread(new Runnable() {
		@Override
		public void run() {
			if (VERBOSE) {
				final double phaseProgress = ((int) Math.floor((1 - (((double) count) / numberOfCombinations)) * 1000)) / 10.0;
				final double coverProgress = ((int) Math.floor(((((double) coveredCount) / numberOfCombinations)) * 1000)) / 10.0;
				final double invalidProgress = ((int) Math.floor(((((double) invalidCount) / numberOfCombinations)) * 1000)) / 10.0;
				final StringBuilder sb = new StringBuilder();

				sb.append(phaseCount);
				sb.append(" - ");
				sb.append(phaseProgress);
				sb.append(" (");
				sb.append(count);
				sb.append(") -- Configurations: ");
				sb.append(incompleteSolutionList.size());
				sb.append(" | ");
				sb.append(completeSolutionList.size());
				sb.append(" -- Covered: ");
				sb.append(coverProgress);
				sb.append(" (");
				sb.append(coveredCount);
				sb.append(")");
				sb.append(" -- Invalid: ");
				sb.append(invalidProgress);
				sb.append(" (");
				sb.append(invalidCount);
				sb.append(")");
				System.out.println(sb.toString());
			}
		}
	});

	public TWiseConfigurationGenerator(CNF cnf, int maxSampleSize, int t, List<List<ClauseList>> nodes) {
		super(cnf, maxSampleSize);
		this.t = t;

		if (cnf.getClauses().isEmpty()) {
			util = new TWiseConfigurationUtil(cnf, null, null);
		} else {
			util = new TWiseConfigurationUtil(cnf, solver, incompleteSolutionList);
			util.computeMIG();
		}

		final UniformRandomConfigurationGenerator randomGenerator = new UniformRandomConfigurationGenerator(cnf, 10000);
		randomGenerator.setAllowDuplicates(false);
		randomGenerator.setSampleSize(1000);
		randomSample = LongRunningWrapper.runMethod(randomGenerator);

		for (final Solution solution : randomSample) {
			util.addSolverSolution(solution.getLiterals());
		}

		expressions = util.cleanClauses(nodes);
		for (final List<ClauseList> list : expressions) {
			for (int i = 1; i < t; i++) {
				final ClauseList pseudoClauseList = new ClauseList();
				pseudoClauseList.add(new LiteralSet());
				list.add(pseudoClauseList);
			}
		}

		for (final List<ClauseList> list : expressions) {
			final Comparator<ClauseList> comparator = new Comparator<ClauseList>() {
				@Override
				public int compare(ClauseList o1, ClauseList o2) {
					final int clauseCountDiff = o1.size() - o2.size();
					if (clauseCountDiff != 0) {
						return clauseCountDiff;
					}
					int clauseLengthDiff = 0;
					for (int i = 0; i < o1.size(); i++) {
						clauseLengthDiff += o2.get(i).size() - o1.get(i).size();
					}
					return clauseLengthDiff;
				}
			};
			Collections.sort(list, comparator);
		}

		solver.useSolutionList(0);
		solver.setSelectionStrategy(SelectionStrategy.ORG);
	}

	@Override
	protected void generate(IMonitor monitor) throws Exception {
		incompleteSolutionList.clear();
		completeSolutionList.clear();

		coveredCount = 0;
		invalidCount = 0;
		phaseCount = 0;
		count = 0;

		buildCombinations(expressions);

		final ArrayList<TWiseConfiguration> resultList = new ArrayList<>(completeSolutionList.size() + incompleteSolutionList.size());
		resultList.addAll(incompleteSolutionList);
		resultList.addAll(completeSolutionList);

		for (final TWiseConfiguration configuration : resultList) {
			configuration.autoComplete();
			addResult(configuration.getSolution());
		}
	}

	private CombinationStatus coverCombinationAll(final ClauseList nextCondition) {
		if (isCovered(nextCondition, completeSolutionList) || isCovered(nextCondition, incompleteSolutionList)) {
			return CombinationStatus.COVERED;
		}

		candidatesList.clear();
		for (final LiteralSet literals : nextCondition) {
			for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
				final TWiseConfiguration candidate = isCandidate(literals, iterator);
				if (candidate != null) {
					candidatesList.add(new Pair<>(literals, candidate));
				}
			}
		}

//		Collections.shuffle(candidatesList, random);
		Collections.sort(candidatesList, candidateLengthComparator);

		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossibleWithinSolverSolution(pair.getKey(), pair.getValue())) {
				select(pair.getValue(), Deduce.NONE, pair.getKey());
				return CombinationStatus.COVERED;
			}
		}

		int validCount = nextCondition.size();
		for (final LiteralSet literals : nextCondition) {
			if (!isCombinationValidSAT(literals.getLiterals())) {
				validCount--;
				for (final Iterator<Pair<LiteralSet, TWiseConfiguration>> iterator = candidatesList.iterator(); iterator.hasNext();) {
					final Pair<LiteralSet, TWiseConfiguration> pair = iterator.next();
					if (pair.getKey().equals(literals)) {
						iterator.remove();
					}
				}
			}
		}
		if (validCount == 0) {
			return CombinationStatus.INVALID;
		}

		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossibleSAT(pair.getKey(), pair.getValue())) {
				select(pair.getValue(), Deduce.NONE, pair.getKey());
				return CombinationStatus.COVERED;
			}
		}

		newConfiguration(nextCondition.get(0));
		return CombinationStatus.COVERED;
	}

	private CombinationStatus coverCombinationSingle(final ClauseList nextCondition) {
		if (isCovered(nextCondition, completeSolutionList) || isCovered(nextCondition, incompleteSolutionList)) {
			return CombinationStatus.COVERED;
		}

		candidatesList.clear();
		for (final LiteralSet literals : nextCondition) {
			for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
				final TWiseConfiguration addCandidate = isCandidate(literals, iterator);
				if (addCandidate != null) {
					candidatesList.add(new Pair<>(literals, addCandidate));
				}
			}
		}

//		Collections.shuffle(candidatesList, random);
		Collections.sort(candidatesList, candidateLengthComparator);

		candidatesList2.clear();
		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossibleWithinSolverSolution(pair.getKey(), pair.getValue())) {
				if (candidatesList2.size() == 1) {
					return CombinationStatus.NOT_COVERED;
				}
				candidatesList2.add(pair);
			}
		}

		if (candidatesList2.size() > 1) {
			return CombinationStatus.NOT_COVERED;
		}

		for (final Pair<LiteralSet, TWiseConfiguration> pair : candidatesList) {
			if (!candidatesList2.contains(pair) && isSelectionPossibleSAT(pair.getKey(), pair.getValue())) {
				if (candidatesList2.size() == 1) {
					return CombinationStatus.NOT_COVERED;
				}
				candidatesList2.add(pair);
			}
		}

		if (candidatesList2.size() == 0) {
			for (final LiteralSet literals : nextCondition) {
				if (isCombinationValidSAT(literals.getLiterals())) {
					newConfiguration(nextCondition.get(0));
					return CombinationStatus.COVERED;
				}
			}
			return CombinationStatus.INVALID;
		} else if (candidatesList2.size() == 1) {
			final Pair<LiteralSet, TWiseConfiguration> first = candidatesList2.iterator().next();
			select(first.getValue(), Deduce.NONE, first.getKey());
			return CombinationStatus.COVERED;
		}
		return CombinationStatus.NOT_COVERED;
	}

	private boolean isCovered(ClauseList condition, Iterable<TWiseConfiguration> solutionList) {
		for (final TWiseConfiguration configuration : solutionList) {
			final Solution solution = configuration.getSolution();
			for (final LiteralSet literals : condition) {
				if (solution.containsAll(literals)) {
					return true;
				}
			}
		}
		return false;
	}

	private TWiseConfiguration isCandidate(final LiteralSet literals, final Iterator<TWiseConfiguration> iterator) {
		final TWiseConfiguration configuration = iterator.next();
		if (configuration.isComplete()) {
			iterator.remove();
			configuration.clear();
			completeSolutionList.add(configuration);
			return null;
		} else {
			return configuration.getSolution().hasConflicts(literals) ? null : configuration;
		}
	}

	private void newConfiguration(final LiteralSet literals) {
		if (completeSolutionList.size() < maxSampleSize) {
			final TWiseConfiguration configuration = new TWiseConfiguration(util);
			select(configuration, Deduce.DP, literals);
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

	private void buildCombinations(List<List<ClauseList>> expressions) {
		final MergeIterator it = new MergeIterator(t, expressions, IteratorID.Lexicographic);
		numberOfCombinations = it.size();
		features = new int[solver.getSatInstance().getVariables().size() + 1];
		lits.clear();
		try {
			samplingMonitor.start();
			final List<ClauseList> combinationListSingle = new ArrayList<>();
			ClauseList combinedCondition = new ClauseList();
			count = coveredCount;
			phaseCount++;
			while (it.hasNext()) {
				combineConditions(it.next(), 0, combinedCondition);
				if (combinedCondition.isEmpty()) {
					invalidCount++;
				} else {
					final CombinationStatus covered = coverCombinationAll(combinedCondition);
					switch (covered) {
					case NOT_COVERED:
						combinationListSingle.add(combinedCondition);
						combinedCondition = new ClauseList();
						break;
					case COVERED:
						coveredCount++;
						combinedCondition.clear();
						break;
					case INVALID:
						invalidCount++;
						combinedCondition.clear();
						break;
					default:
						break;
					}
				}
				count++;
			}

			int coveredIndex = -1;
			boolean changed = true;
			while (changed && ((phaseCount - 1) < 0)) {
				phaseCount++;
				count = coveredCount + invalidCount;
				changed = false;
				for (int i = coveredIndex + 1; i < combinationListSingle.size(); i++) {
					final ClauseList combination = combinationListSingle.get(i);
					final CombinationStatus covered = coverCombinationSingle(combination);
					switch (covered) {
					case COVERED:
						Collections.swap(combinationListSingle, i, ++coveredIndex);
						coveredCount++;
						changed = true;
						break;
					case NOT_COVERED:
						break;
					case INVALID:
						Collections.swap(combinationListSingle, i, ++coveredIndex);
						invalidCount++;
						break;
					default:
						break;
					}
					count++;
				}
			}

			phaseCount++;
			count = coveredCount + invalidCount;
			for (int i = coveredIndex + 1; i < combinationListSingle.size(); i++) {
				final ClauseList combination = combinationListSingle.get(i);
				final CombinationStatus covered = coverCombinationAll(combination);
				switch (covered) {
				case COVERED:
					coveredCount++;
					break;
				case NOT_COVERED:
					break;
				case INVALID:
					invalidCount++;
					break;
				default:
					break;
				}
				count++;
			}
		} finally {
			samplingMonitor.finish();
		}
	}

	private boolean combineConditions(ClauseList[] conditionArray, int t, ClauseList combinedCondition) {
		if (t == conditionArray.length) {
			final int[] combinedLiteralsArray = Arrays.copyOfRange(lits.toArray(), 0, lits.size());
			combinedCondition.add(new LiteralSet(combinedLiteralsArray));
		} else {
			clauseLoop: for (final LiteralSet clause : conditionArray[t]) {
				final int[] literals = clause.getLiterals();
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int x = features[var];
					if ((x != 0) && ((literal ^ x) < 0)) {
						for (i--; i >= 0; i--) {
							final int undoLiteral = literals[i];
							final int var2 = Math.abs(undoLiteral);
							final int y = features[var2];
							final int y2 = y - ((undoLiteral >>> 31) == 0 ? 1 : -1);
							features[var2] = y2;
							if (y2 == 0) {
								lits.pop();
							}
						}
						continue clauseLoop;
					} else {
						features[var] = x + ((literal >>> 31) == 0 ? 1 : -1);
						if (x == 0) {
							lits.push(literal);
						}
					}
				}
				if (!combineConditions(conditionArray, t + 1, combinedCondition)) {
					return false;
				}
				for (int i = 0; i < literals.length; i++) {
					final int literal = literals[i];
					final int var = Math.abs(literal);
					final int y = features[var];
					final int y2 = y - ((literal >>> 31) == 0 ? 1 : -1);
					features[var] = y2;
					if (y2 == 0) {
						lits.pop();
					}
				}
			}
		}
		return true;
	}

	private void select(TWiseConfiguration solution, Deduce deduce, LiteralSet literals) {
		solution.setLiteral(literals.getLiterals());
		if (util.hasSolver()) {
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

	private boolean isSelectionPossibleSAT(final LiteralSet literals, final TWiseConfiguration configuration) {
		if (util.hasSolver()) {
			final ISatSolver localSolver = util.getSolver();
			final int orgAssignmentSize = configuration.setUpSolver(localSolver);
			try {
				final int[] configurationLiterals = configuration.getSolution().getLiterals();
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
		}
		return true;
	}

	private boolean isSelectionPossibleWithinSolverSolution(LiteralSet literals, TWiseConfiguration solution) {
		if (util.hasSolver()) {
			final VecInt solverSolutionIndex = solution.getSolverSolutionIndex();
			for (int i = 0; i < solverSolutionIndex.size(); i++) {
				if (!util.getSolverSolution(solverSolutionIndex.get(i)).hasConflicts(literals)) {
					return true;
				}
			}
			return false;
		}
		return true;
	}

	private boolean isCombinationValidSAT(int[] literals) {
		if (util.hasSolver()) {
			for (final Solution s : randomSample) {
				if (!s.hasConflicts(literals)) {
					return true;
				}
			}
			final ISatSolver solver = util.getSolver();
			final int orgAssingmentLength = solver.getAssignmentSize();
			solver.assignmentPushAll(literals);
			try {
				final SatResult hasSolution = solver.hasSolution();
				switch (hasSolution) {
				case TRUE:
					util.addSolverSolution(solver.getSolution());
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

	public TWiseConfigurationUtil getUtil() {
		return util;
	}

}
