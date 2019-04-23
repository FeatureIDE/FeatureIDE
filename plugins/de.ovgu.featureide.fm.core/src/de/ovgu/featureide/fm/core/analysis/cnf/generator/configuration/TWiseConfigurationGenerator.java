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
import java.util.BitSet;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeSet;

import org.sat4j.core.VecInt;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.ICombinationIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.IteratorFactory.IteratorID;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.iterator.MergeIterator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.MIGComparator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfiguration;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfigurationLengthComparator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.TWiseConfigurationUtil;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.analysis.mig.CollectingVisitor;
import de.ovgu.featureide.fm.core.analysis.mig.Traverser;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.MonitorThread;

/**
 * Generates configurations for a given propositional formula such that t-wise feature coverage is achieved.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationGenerator extends AConfigurationGenerator implements ITWiseConfigurationGenerator {

	private static class Pair<A, B> {
		private final A key;
		private final B value;

		public Pair(A key, B value) {
			this.key = key;
			this.value = value;
		}

		public A getKey() {
			return key;
		}

		public B getValue() {
			return value;
		}
	}

	public static Order order = Order.SORTED;
	public static Phase phase = Phase.SINGLE;

	protected final TWiseConfigurationUtil util;

	protected final List<TWiseConfiguration> incompleteSolutionList = new LinkedList<>();
	protected final List<TWiseConfiguration> completeSolutionList = new ArrayList<>();
	protected final List<LiteralSet> expressionCombinationList = new ArrayList<>();
	protected final List<Integer> combinationLengthList = new ArrayList<>();

	protected final Comparator<TWiseConfiguration> lengthComparator = new TWiseConfigurationLengthComparator();

	protected final int t;
	protected List<List<ClauseList>> expressions;
	protected LiteralSet[] strongHull;

	protected long numberOfCombinations, count, coveredCount, invalidCount, phaseCount;

	private MIGComparator migComparator;

	private int index;
	private BitSet invalid, valid, covered;

	protected final MonitorThread monitorThread = new MonitorThread(new Runnable() {
		@Override
		public void run() {
			if (VERBOSE) {
				final double phaseProgress = ((int) Math.floor(getPhaseProgress() * 1000)) / 10.0;
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

	private double getPhaseProgress() {
		return 1 - (((double) count) / numberOfCombinations);
	}

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

	public TWiseConfigurationGenerator(CNF cnf, int maxSampleSize, int t, List<List<ClauseList>> nodes) {
		super(cnf, maxSampleSize);
		this.t = t;

		incompleteSolutionList.clear();
		completeSolutionList.clear();

		coveredCount = 0;
		invalidCount = 0;
		phaseCount = -1;
		count = 0;

		if (cnf.getClauses().isEmpty()) {
			util = new TWiseConfigurationUtil(cnf, null, null);
		} else {
			util = new TWiseConfigurationUtil(cnf, solver, incompleteSolutionList);
			util.computeMIG();
			migComparator = new MIGComparator(util.getMig());
		}

		expressions = util.cleanClauses(nodes);
		for (final List<ClauseList> list : expressions) {
			for (int i = 1; i < t; i++) {
				final ClauseList pseudoClauseList = new ClauseList();
				pseudoClauseList.add(new LiteralSet());
				list.add(pseudoClauseList);
			}
		}

		switch (order) {
		case RANDOM:
			for (final List<ClauseList> list : nodes) {
				Collections.shuffle(list, util.getRandom());
			}
			break;
		case SORTED:
			for (final List<ClauseList> list : nodes) {
				Collections.shuffle(list, util.getRandom());
				// TODO use MIG
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
			break;
		default:
			throw new AssertionError();
		}

		genHulls();

		numberOfCombinations = getIterator(IteratorID.Lexicographic).size();
	}

	@Override
	protected void generate(IMonitor monitor) throws Exception {
		coverCombinations();

		final ArrayList<TWiseConfiguration> resultList = new ArrayList<>(completeSolutionList.size() + incompleteSolutionList.size());
		resultList.addAll(incompleteSolutionList);
		resultList.addAll(completeSolutionList);

		for (final TWiseConfiguration configuration : resultList) {
			configuration.autoComplete();
			addResult(configuration.getSolution());
		}
	}

	protected ICombinationIterator getIterator(IteratorID id) {
		count = numberOfCombinations;
		phaseCount++;
		return new MergeIterator(t, expressions, id);
	}

	protected void coverCombinations() {
		valid = new BitSet(Math.toIntExact(numberOfCombinations));
		invalid = new BitSet(Math.toIntExact(numberOfCombinations));
		covered = new BitSet(Math.toIntExact(numberOfCombinations));
		try {
			monitorThread.start();

			{
				final ICombinationIterator it = getIterator(IteratorID.Lexicographic);
				comboLoop: while (it.hasNext()) {
					final Iterable<LiteralSet> nextCombinations = nextCombination(it, true);
					if (nextCombinations == null) {
						continue comboLoop;
					}

					final List<Pair<LiteralSet, List<TWiseConfiguration>>> candidatesList = new LinkedList<>();

					for (final LiteralSet literals : nextCombinations) {
						final List<TWiseConfiguration> candidates = new ArrayList<>();
						candidatesList.add(new Pair<>(literals, candidates));
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration addCandidate = isCandidate(literals, iterator);
							if (addCandidate != null) {
								candidates.add(addCandidate);
							}
						}
						Collections.sort(candidates, lengthComparator);

						for (final TWiseConfiguration configuration : candidates) {
							if (selectionPossibleWithinSolverSolution(configuration, literals)) {
								select(configuration, Deduce.NONE, literals);
								continue comboLoop;
							}
						}
					}

					for (final Iterator<Pair<LiteralSet, List<TWiseConfiguration>>> iterator = candidatesList.iterator(); iterator.hasNext();) {
						final Pair<LiteralSet, List<TWiseConfiguration>> pair = iterator.next();
						final LiteralSet literals = pair.getKey();
						if (isCombinationValidSAT(literals)) {
							for (final TWiseConfiguration configuration : pair.getValue()) {
								if (selectionPossibleSAT(literals, configuration)) {
									select(configuration, Deduce.NONE, literals);
									continue comboLoop;
								}
							}
						} else {
							iterator.remove();
						}
					}

					if (candidatesList.isEmpty()) {
						invalid.set(index);
						invalidCount++;
					} else {
						newConfiguration(candidatesList.get(0).getKey());
						continue comboLoop;
					}
				}
			}

			// -- 4 --
			{
				final ICombinationIterator it = getIterator(IteratorID.Lexicographic);
				comboLoop: while (it.hasNext()) {
					final Iterable<LiteralSet> nextCombinations = nextCombination(it, false);
					if (nextCombinations == null) {
						continue comboLoop;
					}

					final List<Pair<LiteralSet, List<TWiseConfiguration>>> candidatesList = new LinkedList<>();

					for (final LiteralSet literals : nextCombinations) {
						final List<TWiseConfiguration> candidates = new ArrayList<>();
						candidatesList.add(new Pair<>(literals, candidates));
						for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
							final TWiseConfiguration addCandidate = isCandidate(literals, iterator);
							if (addCandidate != null) {
								candidates.add(addCandidate);
							}
						}
						Collections.sort(candidates, lengthComparator);

						for (final TWiseConfiguration configuration : candidates) {
							if (selectionPossibleWithinSolverSolution(configuration, literals)) {
								select(configuration, Deduce.NONE, literals);
								continue comboLoop;
							}
						}
					}

					for (final Iterator<Pair<LiteralSet, List<TWiseConfiguration>>> iterator = candidatesList.iterator(); iterator.hasNext();) {
						final Pair<LiteralSet, List<TWiseConfiguration>> pair = iterator.next();
						final LiteralSet literals = pair.getKey();
						if (isCombinationValidSAT(literals)) {
							for (final TWiseConfiguration configuration : pair.getValue()) {
								if (selectionPossibleSAT(literals, configuration)) {
									select(configuration, Deduce.NONE, literals);
									continue comboLoop;
								}
							}
						} else {
							iterator.remove();
						}
					}

					if (!candidatesList.isEmpty()) {
						newConfiguration(candidatesList.get(0).getKey());
						continue comboLoop;
					}
				}
			}
		} finally {
			monitorThread.finish();
		}
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

	private void generateRandomSolutions(int count) {
		final ISatSolver solver = util.getSolver();
		solver.setSelectionStrategy(SelectionStrategy.RANDOM);
		final int orgAssignmentSize = solver.getAssignmentSize();
		try {
			for (int i = 0; i < count; i++) {
				util.addSolverSolution(solver.findSolution());
				solver.shuffleOrder(util.getRandom());
			}
		} finally {
			solver.assignmentClear(orgAssignmentSize);
		}
	}

	private void genHulls() {
		strongHull = new LiteralSet[util.getMig().getAdjList().size()];

		for (final Vertex vertex : util.getMig().getAdjList()) {
			final int literalSet = vertex.getVar();
			final Traverser traverser = new Traverser(util.getMig());
			traverser.setModel(new int[util.getMig().getAdjList().size()]);
			final CollectingVisitor visitor = new CollectingVisitor();
			traverser.setVisitor(visitor);
			traverser.traverse(literalSet);
			final VecInt strong = visitor.getResult()[0];
			strongHull[vertex.getId()] = new LiteralSet(Arrays.copyOf(strong.toArray(), strong.size()));
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
				Collections.sort(incompleteSolutionList, lengthComparator);
			}
		}
	}

	private Iterable<LiteralSet> nextCombination(final ICombinationIterator it, boolean ignoreDNFsWithMultipleClauses) {
		final ClauseList[] clauseArray = it.next();
		count--;
		index = (int) it.getIndex();
		if (invalid.get(index) || covered.get(index)) {
			return null;
		}
		if (ignoreDNFsWithMultipleClauses) {
			for (final ClauseList expression : clauseArray) {
				if (expression.size() > 1) {
					return null;
				}
			}
		}

		completeSolutionLoop: for (final TWiseConfiguration configuration : completeSolutionList) {
			for (int l = 0; l < clauseArray.length; l++) {
				if (!isSelected(configuration, clauseArray[l])) {
					continue completeSolutionLoop;
				}
			}
			coveredCount++;
			covered.set(index);
			return null;
		}

		solutionLoop: for (final TWiseConfiguration configuration : incompleteSolutionList) {
			for (int l = 0; l < clauseArray.length; l++) {
				if (!isSelected(configuration, clauseArray[l])) {
					continue solutionLoop;
				}
			}
			coveredCount++;
			covered.set(index);
			return null;
		}

		return getNextCombinations(clauseArray);
	}

	public boolean selectionPossibleSAT(final LiteralSet literals, final TWiseConfiguration configuration) {
		if (util.hasSolver()) {
			final ISatSolver localSolver = util.getSolver();
			localSolver.setSelectionStrategy(SelectionStrategy.RANDOM);
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
					} else {
						util.addSolverSolution(localSolver.getInternalSolution());
						localSolver.shuffleOrder(util.getRandom());
					}
				}
			} finally {
				localSolver.assignmentClear(orgAssignmentSize);
			}
		}
		return true;
	}

	private boolean isSelected(TWiseConfiguration configuration, ClauseList clauseList) {
		for (final LiteralSet clause : clauseList) {
			if (configuration.getSolution().containsAll(clause)) {
				return true;
			}
		}
		return false;
	}

	protected void select(TWiseConfiguration solution, Deduce deduce, LiteralSet literals) {
		coveredCount++;
		covered.set(index);
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

	protected boolean selectionPossibleWithinSolverSolution(TWiseConfiguration solution, LiteralSet literals) {
		if (util.hasSolver()) {
			// test whether there is a possible solution that already contains the combination
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

	protected boolean isCombinationValidSAT(LiteralSet literals) {
		if (util.hasSolver()) {
			for (final Solution s : util.getSolverSolutions()) {
				if (s == null) {
					break;
				}
				if (!s.hasConflicts(literals)) {
					return true;
				}
			}
			final ISatSolver solver = util.getSolver();
			solver.setSelectionStrategy(SelectionStrategy.RANDOM);
			final int orgAssingmentLength = solver.getAssignmentSize();
			solver.assignmentPushAll(literals.getLiterals());
			try {
				if (solver.hasSolution() != SatResult.TRUE) {
					invalidCount++;
					return false;
				} else {
					util.addSolverSolution(solver.getInternalSolution());
					solver.shuffleOrder(util.getRandom());
				}
			} finally {
				solver.assignmentClear(orgAssingmentLength);
			}
		}
		return true;
	}

	private Iterable<LiteralSet> getNextCombinations(ClauseList[] indexArray) {
		final int t = indexArray.length;
		final int[] clauseIndex = new int[t];
		clauseIndex[0] = -1;
		int i = 0;
		expressionCombinationList.clear();
		combinationLengthList.clear();
		combinationLoop: while (i < t) {
			// TODO gray code may be faster
			for (i = 0; i < t; i++) {
				final int cindex = clauseIndex[i];
				if (cindex == (indexArray[i].size() - 1)) {
					clauseIndex[i] = 0;
				} else {
					clauseIndex[i] = cindex + 1;

					final TreeSet<Integer> newLiteralSet = new TreeSet<>();
					for (int j = 0; j < t; j++) {
						for (final int literal : indexArray[j].get(clauseIndex[j]).getLiterals()) {
							newLiteralSet.add(literal);
						}
					}

					final int[] combinationLiterals = new int[newLiteralSet.size()];
					int j = 0;
					for (final Integer literal : newLiteralSet) {
						combinationLiterals[j++] = literal;
					}
					final LiteralSet literalSet = new LiteralSet(combinationLiterals);

					for (final int literal : combinationLiterals) {
						final LiteralSet stronglyConnectedLiterals = strongHull[util.getMig().getVertex(literal).getId()];
						if (stronglyConnectedLiterals.hasConflicts(literalSet)) {
							continue combinationLoop;
						}
						for (final int stronglyConnectedLiteral : stronglyConnectedLiterals.getLiterals()) {
							newLiteralSet.add(stronglyConnectedLiteral);
						}
					}

					expressionCombinationList.add(literalSet);
					combinationLengthList.add(newLiteralSet.size());
				}
			}
		}
		final Integer[] sortedIndex = Functional.getSortedIndex(combinationLengthList, new Comparator<Integer>() {
			@Override
			public int compare(Integer o1, Integer o2) {
				return o1 - o2;
			}
		});

		final List<LiteralSet> sortedList = new ArrayList<>(expressionCombinationList.size());
		for (int j = 0; j < sortedIndex.length; j++) {
			sortedList.add(expressionCombinationList.get(sortedIndex[j]));
		}
		return sortedList;
	}

//	private class ExpressionCombination implements Iterator<LiteralSet> {
//		private final int[] clauseIndex;
//		private final int t;
//
//		private ClauseList[] tempExpressions;
//		private int i;
//
//		public ExpressionCombination(int t) {
//			t = t;
//			clauseIndex = new int[t];
//		}
//
//		public void init(ClauseList[] indexArray) {
//			tempExpressions = indexArray;
//		}
//
//		public LiteralSet reset() {
//			Arrays.fill(clauseIndex, 0);
//			clauseIndex[0] = -1;
//			i = 0;
//			return next();
//		}
//
//		@Override
//		public boolean hasNext() {
//			return i < t;
//		}
//
//		@Override
//		public LiteralSet next() {
//			combinationLoop: while (i < t) {
//				// TODO gray code may be faster
//				for (i = 0; i < t; i++) {
//					final int cindex = clauseIndex[i];
//					if (cindex == (tempExpressions[i].size() - 1)) {
//						clauseIndex[i] = 0;
//					} else {
//						clauseIndex[i] = cindex + 1;
//
//						final TreeSet<Integer> newLiteralSet = new TreeSet<>();
//						for (int j = 0; j < t; j++) {
//							for (final int literal : tempExpressions[j].get(clauseIndex[j]).getLiterals()) {
//								newLiteralSet.add(literal);
//							}
//						}
//
//						final int[] combinationLiterals = new int[newLiteralSet.size()];
//						int j = 0;
//						for (final Integer literal : newLiteralSet) {
//							combinationLiterals[j++] = literal;
//						}
//						final LiteralSet literalSet = new LiteralSet(combinationLiterals);
//
//						for (final int literal : combinationLiterals) {
//							if (strongHull[util.getMig().getVertex(literal).getId()].hasConflicts(literalSet)) {
//								continue combinationLoop;
//							}
//						}
//
//						return literalSet;
//					}
//				}
//			}
//			return null;
//		}
//
//	}

	public TWiseConfigurationUtil getUtil() {
		return util;
	}

}
