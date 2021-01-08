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
package de.ovgu.featureide.fm.core.analysis.mig;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Random;
import java.util.Set;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet.Order;
import de.ovgu.featureide.fm.core.analysis.cnf.Variables;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver.SelectionStrategy;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigurationFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.CoreFactoryWorkspaceLoader;
import de.ovgu.featureide.fm.core.base.impl.DefaultConfigurationFactory;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.sxfm.SXFMFormat;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 *
 * @author rahel
 */
public class IncrementalMIGBuilder implements LongRunningMethod<ModalImplicationGraph> {

	/**
	 * For sorting clauses by length. Starting with the longest.
	 */
	private static final Comparator<LiteralSet> lengthComparator = new Comparator<LiteralSet>() {

		@Override
		public int compare(LiteralSet o1, LiteralSet o2) {
			return o1.getLiterals().length - o2.getLiterals().length;
		}
	};

	private CNF oldCNF;
	private CNF newCNF;
	private CNF newCNFclean;
	private Set<LiteralSet> removedClauses;
	private final Set<LiteralSet> strongEdges = new HashSet<>();
	private Set<LiteralSet> addedClauses;
	private Set<LiteralSet> redundantClauses;
	private ModalImplicationGraph newMig;
	private ModalImplicationGraph oldMig;
	private int numberOfVariablesNew;
	private byte[] dfsMark;
	private MIGBuilder migBuilder;
	private Variables variables;
	private boolean detectStrong = false;
	private final boolean checkRedundancy = true;
	private static String dateiname = "";
	private int satCall = 0;
	ModalImplicationGraph testMIG;
	final ArrayDeque<Integer> dfsStack = new ArrayDeque<>();
	Set<LiteralSet> possiblyImplicitStrongEdges = new HashSet<LiteralSet>();
	List<LiteralSet> throughImplStrongAffected;

	public IncrementalMIGBuilder(CNF satInstance) {
		newCNF = satInstance;
		numberOfVariablesNew = satInstance.getVariables().size();
		dfsMark = new byte[numberOfVariablesNew * 2];
	}

	public static void main(String[] args) throws Exception {
//		for (int i = 0; i < 3; i++) {
		installLibraries();
//		final File file = new File(
//				"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\FeatureIDE\\FeatureIDE\\plugins\\de.ovgu.featureide.examples\\featureide_examples\\FeatureModels\\FinancialServices01\\history");
//		final File[] fileArray = file.listFiles();
//		for (int i = 0; i < fileArray.length; i++) {
//			if (i < 2) {
//
//			} else {
//				dateiname = fileArray[i].getName();
//				final IFeatureModel fm = FeatureModelManager.load(Paths.get(fileArray[i].getPath()));
//				final CNF newCnfPrep = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF().clone();
//				final IncrementalMIGBuilder incMigbuilder = new IncrementalMIGBuilder(newCnfPrep);
//				incMigbuilder.buildPreconditions(FeatureModelManager.load(Paths.get(fileArray[i - 1].getPath())));
//				incMigbuilder.execute(new NullMonitor<ModalImplicationGraph>());
//			}
//		}
	}

	private void buildPreconditions() {
		final IFeatureModel fm = FeatureModelManager.load(Paths.get(
				"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\FeatureIDE\\FeatureIDE\\plugins\\de.ovgu.featureide.examples\\featureide_examples\\FeatureModels\\FinancialServices01\\history\\2017-09-28.xml"));
		oldCNF = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF();
		final Set<String> allVariables = new HashSet<>(Arrays.asList(oldCNF.getVariables().getNames()).subList(1, oldCNF.getVariables().getNames().length));
		allVariables.addAll(Arrays.asList(newCNF.getVariables().getNames()).subList(1, newCNF.getVariables().getNames().length));
		variables = new Variables(allVariables);
		oldCNF = oldCNF.adapt(variables);
		newCNF = newCNF.adapt(variables);
		assert Objects.equals(oldCNF.getVariables(), newCNF.getVariables());
		newCNFclean = new CNF(variables);
		migBuilder = new MIGBuilder(oldCNF);
		migBuilder.setCheckRedundancy(checkRedundancy);
		migBuilder.setDetectStrong(detectStrong);
		oldMig = LongRunningWrapper.runMethod(migBuilder);
		redundantClauses = migBuilder.getRedundantClauses();
		newMig = new ModalImplicationGraph(declareMigSize(oldCNF.getVariables().size(), numberOfVariablesNew) * 2);
		newMig.copyValues(oldMig);
	}

	public int declareMigSize(int numberOfVariablesOld, int numberOfVariablesNew) {
		return numberOfVariablesNew > numberOfVariablesOld ? numberOfVariablesNew : numberOfVariablesOld;
	}

	@Override
	public ModalImplicationGraph execute(IMonitor<ModalImplicationGraph> monitor) throws Exception {
		Set<LiteralSet> affectedClauses = new HashSet<>();

		printOldMig();

		oldCNF = new CNF(variables, migBuilder.getClausesInMig());

		oldCNF.getClauses().forEach(c -> c.setOrder(LiteralSet.Order.NATURAL));
		newCNF.getClauses().forEach(c -> c.setOrder(LiteralSet.Order.NATURAL));

		// zeitzähler
		final long startTime = System.nanoTime();

		// remove transitive strong edges from the MIG
		final Set<LiteralSet> transStrongEdges = oldMig.getTransitiveStrongEdges();
		for (final LiteralSet literalset : migBuilder.getClausesInMig()) {
			if (transStrongEdges.contains(literalset)) {
				transStrongEdges.remove(literalset);
			}
		}
		for (final LiteralSet literalSet : transStrongEdges) {
			newMig.removeClause(literalSet);
		}
		final long removeTransStrongEdges = System.nanoTime();

		if (!oldMig.getTransitiveWeakEdges().isEmpty()) {
			final Set<LiteralSet> transWeakEdges = oldMig.getTransitiveWeakEdges();
			for (final LiteralSet literalset : migBuilder.getClausesInMig()) {
				if (transWeakEdges.contains(literalset)) {
					transWeakEdges.remove(literalset);
				}
			}
			for (final LiteralSet literalSet : transWeakEdges) {
				newMig.getTransitiveWeakEdges().remove(literalSet);
			}
		}
		final long removeTransWeakEdges = System.nanoTime();

		// handle core/dead features
		calculateDeadAndCoreFeatures();
		final long deadCoreFeatures = System.nanoTime();

		// clean new CNF
		sortOutClauses();
		final long cleanCNF = System.nanoTime();

		// check old implicit strong edges
		if (!oldMig.getImplicitStrongEdges().isEmpty()) {
			final ISatSolver solver = new AdvancedSatSolver(newCNFclean);
			solver.useSolutionList(0);
			solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
			for (final LiteralSet implicitStrongEdge : oldMig.getImplicitStrongEdges()) {
				final int[] literals = implicitStrongEdge.getLiterals();
				for (int i = 0; i < literals.length; i++) {
					final int firstLiteral = literals[i];
					solver.assignmentPush(-firstLiteral);
					for (int j = i + 1; j < literals.length; j++) {
						final int secondLiteral = literals[j];
						solver.assignmentPush(-secondLiteral);
						final LiteralSet newImplicitStrongEdge = new LiteralSet(firstLiteral, secondLiteral);
						satCall++;
						switch (solver.hasSolution()) {
						case FALSE:
							newMig.getImplicitStrongEdges().add(newImplicitStrongEdge);
							newCNFclean.addClause(newImplicitStrongEdge);
							solver.addClause(newImplicitStrongEdge);
							strongEdges.add(newImplicitStrongEdge);
							break;
						case TIMEOUT:
							break;
						case TRUE:
							newMig.removeClause(newImplicitStrongEdge);
							for (final LiteralSet clause : newCNFclean.getClauses()) {
								if ((clause.size() > 3) && (clause.containsAll(newImplicitStrongEdge))) {
									newMig.addClause(clause);
								}
							}
							break;
						}
						solver.assignmentPop();
					}
					solver.assignmentPop();
				}
			}
		}
		final long checkOldImplicitStrongEdges = System.nanoTime();

		// calculate CNF difference
		calculateCNFDifference();
		final long cnfDiff = System.nanoTime();

		// remove clauses from MIG
		final Set<LiteralSet> remRed = new HashSet<>(redundantClauses);
		redundantClauses.removeAll(removedClauses);
		removedClauses.removeAll(remRed);
		for (final LiteralSet clause : removedClauses) {
			newMig.removeClause(clause);
		}
		final long remClauses = System.nanoTime();

		long prevRedClauses = System.nanoTime();
		if (checkRedundancy) {
			// handle previously redundant clauses
			if (!redundantClauses.isEmpty() && !removedClauses.isEmpty()) {
				handlePreviouslyRedundant(new ArrayList<>(redundantClauses));
			}
			prevRedClauses = System.nanoTime();

			// handle newly redundant clauses
			final Set<LiteralSet> notRedundantClauses = new HashSet<>(newCNFclean.getClauses());
			if (!redundantClauses.isEmpty()) {
				notRedundantClauses.removeAll(redundantClauses);
			}
			affectedClauses = new HashSet<>(getThroughLiteralsAffectedClauses(new ArrayList<>(addedClauses), new ArrayList<>(notRedundantClauses)));
			handleNewlyRedundant(new ArrayList<>(affectedClauses));
		}
		final long newlyRedClauses = System.nanoTime();

		// add clauses
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNFclean, false));
		final Set<LiteralSet> notAddedClauses = new LinkedHashSet<>(newCNFclean.getClauses());
		notAddedClauses.removeAll(addedClauses);
		newSolver.addClauses(notAddedClauses);
		final List<LiteralSet> adddedClausesList = new ArrayList<>(addedClauses);
		Collections.sort(adddedClausesList, lengthComparator);
		for (final LiteralSet clause : adddedClausesList) {
			if (checkRedundancy) {
				if ((clause.getLiterals().length < 3) || !isRedundant(newSolver, clause)) {
					newMig.addClause(clause);
					newSolver.addClause(clause);
					if (clause.getLiterals().length > 2) {
						possiblyImplicitStrongEdges.add(clause);
					} else {
						strongEdges.add(clause);
					}
				} else {
					redundantClauses.add(clause);
				}
			} else {
				if (clause.getLiterals().length > 2) {
					possiblyImplicitStrongEdges.add(clause);
				}
				newMig.addClause(clause);
			}
		}
		final long addClauses = System.nanoTime();

		long completeDfsStrong = System.nanoTime();
		long completeDfsWeak = System.nanoTime();
		long completeImplicitStrong = System.nanoTime();
		numberOfVariablesNew = newCNF.getVariables().size();
		dfsMark = new byte[numberOfVariablesNew * 2];
		throughImplStrongAffected = new ArrayList<LiteralSet>(newCNFclean.getClauses()); // mit mehr als 3!!
		if (detectStrong) {
			dfsStrong();
			completeDfsStrong = System.nanoTime();
			dfsWeak();
			completeDfsWeak = System.nanoTime();
			possiblyImplicitStrongEdges
					.addAll(getThroughLiteralsAffectedClauses(new ArrayList<LiteralSet>(possiblyImplicitStrongEdges), throughImplStrongAffected));
			detectStrongEdges(possiblyImplicitStrongEdges);
			completeImplicitStrong = System.nanoTime();
		}

		dfsMark = new byte[numberOfVariablesNew * 2];
		dfsStrong();
		// zeitzähler
		final long endTime = System.nanoTime();

		System.out.println("Benötigte Zeit beim incremental: " + (endTime - startTime));

		final long startTimeOld = System.nanoTime();

		final MIGBuilder migBuilder = new MIGBuilder(newCNF);
		testMIG = new ModalImplicationGraph();
		migBuilder.setCheckRedundancy(checkRedundancy);
		migBuilder.setDetectStrong(detectStrong);
		try {
			testMIG = migBuilder.execute(new NullMonitor<ModalImplicationGraph>());
		} catch (final Exception e) {
			e.printStackTrace();
		}

		final long endTimeOld = System.nanoTime();

		System.out.println("Benötigte Zeit beim neu Berechnen: " + (endTimeOld - startTimeOld));
		System.out.println("Zeitsparen durch incremental: " + (endTimeOld - startTimeOld - (endTime - startTime)));

		compare(newMig, testMIG);

		printTimes(startTime, removeTransStrongEdges, removeTransWeakEdges, deadCoreFeatures, cleanCNF, checkOldImplicitStrongEdges, cnfDiff, remClauses,
				prevRedClauses, newlyRedClauses, addClauses, completeDfsStrong, completeDfsWeak, endTime, endTimeOld, startTimeOld, migBuilder);

		printNewMig();

		printCalculatedMig(testMIG);

		printClauses();

		return newMig;
	}

	private void detectStrongEdges(Set<LiteralSet> possibilyImplicitStrongEdges) {
		final ISatSolver solver = new AdvancedSatSolver(newCNFclean);
		solver.useSolutionList(0);
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final Set<LiteralSet> literalSetsImpl = new HashSet<>();
		for (final LiteralSet implicitStrongEdge : possibilyImplicitStrongEdges) {
			final int[] literals = implicitStrongEdge.getLiterals();
			for (int i = 0; i < literals.length; i++) {
				for (int j = i + 1; j < literals.length; j++) {
					final LiteralSet literalSet = new LiteralSet(new int[] { literals[i], literals[j] }, Order.NATURAL);
					final LiteralSet literalSet2 = new LiteralSet(new int[] { -literals[i], -literals[j] }, Order.NATURAL);
					if (!strongEdges.contains(literalSet)) {
						literalSetsImpl.add(literalSet);
					}
					if (!strongEdges.contains(literalSet2)) {
						literalSetsImpl.add(literalSet2);
					}
				}
			}
		}
		for (final LiteralSet implicitStrongEdge : literalSetsImpl) {
			for (final int firstLiteral : implicitStrongEdge.getLiterals()) {
				solver.assignmentPush(-firstLiteral);
				m: for (final int secondLiteral : implicitStrongEdge.getLiterals()) {
					if (secondLiteral == firstLiteral) {
						continue m;
					}
					solver.assignmentPush(-secondLiteral);
					satCall++;
					switch (solver.hasSolution()) {
					case FALSE:
						final LiteralSet newImplicitStrongEdge = new LiteralSet(new int[] { firstLiteral, secondLiteral }, Order.NATURAL);
						newMig.addClause(newImplicitStrongEdge);
						newMig.getImplicitStrongEdges().add(newImplicitStrongEdge);
						solver.addClause(newImplicitStrongEdge);
						solver.assignmentPop();
						break;
					case TIMEOUT:
						solver.assignmentPop();
						break;
					case TRUE:
						solver.assignmentPop();
						break;
					}
				}
				solver.assignmentPop();
			}
		}
	}

	private void dfsWeak() {
		dfsStack.clear();
		Arrays.fill(dfsMark, (byte) 0);
		for (int nextIndex = 1; nextIndex <= numberOfVariablesNew; nextIndex++) {
			dfsWeak(nextIndex);
			mark();
			dfsWeak(-nextIndex);
			mark();
			dfsMark[nextIndex - 1] = 2;
		}
	}

	private void dfsWeak(int curVar) {
		final int curIndex = Math.abs(curVar) - 1;

		if ((dfsMark[curIndex] & 1) != 0) {
			return;
		}
		dfsMark[curIndex] |= 1;

		final int size = dfsStack.size();
		int curVarAdjListPos = 0;

		if (size > 1) {
			final LiteralSet newTransitiveWeakEdge = new LiteralSet(-dfsStack.getFirst(), curVar);
			newMig.getTransitiveWeakEdges().add(newTransitiveWeakEdge);
			if (!oldMig.getTransitiveWeakEdges().contains(newTransitiveWeakEdge)) {
				throughImplStrongAffected.add(newTransitiveWeakEdge);
			}
		}

		if ((size > 0) && ((dfsMark[Math.abs(dfsStack.getLast()) - 1] & 2) != 0)) {
			return;
		}
		dfsStack.addLast(curVar);

		if (curVar > 0) {
			curVarAdjListPos = (curVar * 2) - 1;
		} else {
			curVarAdjListPos = (Math.abs(curVar) * 2) - 2;
		}

		for (final int complexClause : newMig.getAdjList().get(curVarAdjListPos).getComplexClauses()) {
			for (final int weakEdge : newMig.getComplexClauses().get(complexClause).getLiterals()) {
				dfsWeak(weakEdge);
			}
		}
		for (final int strongEdge : newMig.getAdjList().get(curVarAdjListPos).getStrongEdges()) {
			dfsWeak(strongEdge);
		}
		dfsStack.removeLast();
	}

	private void sortOutClauses() {
		outer: for (final LiteralSet clause : newCNF.getClauses()) {
			final int[] literals = clause.getLiterals();
			final HashSet<Integer> literalSet = new HashSet<>(literals.length << 1);

			// Sort out dead and core features
			int childrenCount = clause.size();
			for (int i = 0; i < childrenCount; i++) {
				final int var = literals[i];
				int coreB = 0;
				if (newMig.getVertex(var).isCore()) {
					coreB = Math.abs(var);
				} else if (newMig.getVertex(var).isDead()) {
					coreB = -Math.abs(var);
				}

				if (coreB > 0) {
					// Clause is satisfied
					continue outer;
				} else if (coreB < 0) {
					// Current literal is unsatisfied (dead or core feature)
					if (childrenCount <= 2) {
						continue outer;
					}
					childrenCount--;
					// Switch literals (faster than deletion within an
					// array)
					literals[i] = literals[childrenCount];
					literals[childrenCount] = var;
					i--;
				} else {
					if (literalSet.contains(-var)) {
						continue outer;
					} else {
						literalSet.add(var);
					}
				}
			}
			final int[] literalArray = new int[literalSet.size()];
			int i = 0;
			for (final int lit : literalSet) {
				literalArray[i++] = lit;
			}
			newCNFclean.addClause(new LiteralSet(literalArray));
		}
	}

	private void calculateDeadAndCoreFeatures() {
		final ISatSolver solver = new AdvancedSatSolver(newCNF);
		solver.useSolutionList(0);

		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);
		final int[] solution1 = solver.findSolution();
		solver.setSelectionStrategy(SelectionStrategy.NEGATIVE);
		final int[] solution2 = solver.findSolution();
		LiteralSet.resetConflicts(solution1, solution2);

		for (int i = 0; i < solution1.length; i++) {
			final int varX = solution1[i];
			if (varX != 0) {
				solver.assignmentPush(-varX);
				satCall++;
				switch (solver.hasSolution()) {
				case FALSE:
					solver.assignmentReplaceLast(varX);
					newMig.getVertex(varX).setCore(true);
					newMig.getVertex(varX).setDead(false);
					newMig.getVertex(-varX).setDead(true);
					newMig.getVertex(-varX).setCore(false);
					newCNFclean.addClause(new LiteralSet(varX));
					break;
				case TIMEOUT:
					solver.assignmentPop();
					break;
				case TRUE:
					solver.assignmentPop();
					final Vertex vertexPos = newMig.getVertex(i + 1);
					final Vertex vertexNeg = newMig.getVertex(-(i + 1));
					vertexPos.setCore(false);
					vertexPos.setDead(false);
					vertexNeg.setCore(false);
					vertexNeg.setDead(false);
					LiteralSet.resetConflicts(solution1, solver.getSolution());
					solver.shuffleOrder(new Random(112358));
					break;
				}
			} else {
				// falls vorher core oder dead und jetzt nicht mehr
				final Vertex vertexPos = newMig.getVertex(i + 1);
				final Vertex vertexNeg = newMig.getVertex(-(i + 1));
				vertexPos.setCore(false);
				vertexPos.setDead(false);
				vertexNeg.setCore(false);
				vertexNeg.setDead(false);
			}
		}
	}

	private void calculateDeadAndCoreFeaturesDC() {
		// TODO
	}

	private void mark() {
		for (int i = 0; i < dfsMark.length; i++) {
			dfsMark[i] &= 2;
		}
	}

	// TODO: Kann man da auch was sparen wegen evolution?
	private void dfsStrong() {
		for (int nextIndex = 1; nextIndex <= numberOfVariablesNew; nextIndex++) {
			dfsStrong(nextIndex);
			mark();
			dfsStrong(-nextIndex);
			mark();
			dfsMark[nextIndex - 1] = 2;
		}
	}

	private void dfsStrong(int curVar) {
		final int curIndex = Math.abs(curVar) - 1;

		if ((dfsMark[curIndex] & 1) != 0) {
			return;
		}
		dfsMark[curIndex] |= 1;

		final int size = dfsStack.size();
		int curVarAdjListPos = 0;

		if (size > 1) {
			final LiteralSet newTransitiveStrongEdge = new LiteralSet(-dfsStack.getFirst(), curVar);
			newMig.addClause(newTransitiveStrongEdge);
			newMig.getTransitiveStrongEdges().add(newTransitiveStrongEdge);
			strongEdges.add(newTransitiveStrongEdge);
		}

		if ((size > 0) && ((dfsMark[Math.abs(dfsStack.getLast()) - 1] & 2) != 0)) {
			return;
		}

		dfsStack.addLast(curVar);
		if (curVar > 0) {
			curVarAdjListPos = (curVar * 2) - 1;
		} else {
			curVarAdjListPos = (Math.abs(curVar) * 2) - 2;
		}
		for (final int strongEdge : newMig.getAdjList().get(curVarAdjListPos).getStrongEdges()) {
			dfsStrong(strongEdge);
		}
		dfsStack.removeLast();
	}

	public void calculateCNFDifference() {
		removedClauses = new HashSet<>(oldCNF.getClauses());
		addedClauses = new HashSet<>(newCNFclean.getClauses());
		removedClauses.removeAll(addedClauses);
		addedClauses.removeAll(new HashSet<>(oldCNF.getClauses()));
	}

	public List<LiteralSet> getThroughLiteralsAffectedClauses(List<LiteralSet> startClauses, List<LiteralSet> possiblyAffectedClauses) {
		final List<LiteralSet> affectedClauses = new ArrayList<>();
		final LinkedHashSet<Integer> startClauseVariables = new LinkedHashSet<>();
		for (final LiteralSet startClause : startClauses) {
			for (final int variable : startClause.getVariables().getLiterals()) {
				startClauseVariables.add(variable);
			}
		}
		final List<LiteralSet> possiblyUnaffectedClauses = new ArrayList<>();
		for (final LiteralSet possiblyAffectedLiteralSet : possiblyAffectedClauses) {
			for (final int variable : possiblyAffectedLiteralSet.getVariables().getLiterals()) {
				if (startClauseVariables.contains(variable)) {
					affectedClauses.add(possiblyAffectedLiteralSet);
				} else {
					possiblyUnaffectedClauses.add(possiblyAffectedLiteralSet);
				}
			}
		}
		return affectedClauses;
	}

	public List<LiteralSet> getAllAffectedClauses(List<LiteralSet> startClauses, List<LiteralSet> possiblyAffectedClauses) {
		final List<LiteralSet> affectedClauses = new ArrayList<>();
		final LinkedHashSet<Integer> startClauseVariables = new LinkedHashSet<>();
		for (final LiteralSet startClause : startClauses) {
			for (final int variable : startClause.getVariables().getLiterals()) {
				startClauseVariables.add(variable);
			}
		}

		final List<LiteralSet> possiblyUnaffectedClauses = new ArrayList<>();
		for (final LiteralSet possiblyAffectedLiteralSet : possiblyAffectedClauses) {
			for (final int variable : possiblyAffectedLiteralSet.getVariables().getLiterals()) {
				if (startClauseVariables.contains(variable)) {
					affectedClauses.add(possiblyAffectedLiteralSet);
				} else {
					possiblyUnaffectedClauses.add(possiblyAffectedLiteralSet);
				}
			}
		}
		if (!affectedClauses.isEmpty()) {
			affectedClauses.addAll(getAllAffectedClauses(affectedClauses, possiblyUnaffectedClauses));
		}
		return affectedClauses;

	}

	public void handlePreviouslyRedundant(List<LiteralSet> clauses) {
		Collections.sort(clauses, lengthComparator);
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNFclean, false));
		final Set<LiteralSet> notAffectedClauses = new LinkedHashSet<>(newCNFclean.getClauses());
		notAffectedClauses.removeAll(clauses); // vermutlich unnötig, nochma drüber nachdenken.
		newSolver.addClauses(notAffectedClauses);
		for (final LiteralSet clause : clauses) {
			if (!isRedundant(newSolver, clause)) {
				newMig.addClause(clause);
				redundantClauses.remove(clause);
				newSolver.addClause(clause);
			}
		}
	}

	public void handleNewlyRedundant(List<LiteralSet> clauses) {
		Collections.sort(clauses, lengthComparator);
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNFclean, false));
		final Set<LiteralSet> notAffectedClauses = new LinkedHashSet<>(newCNFclean.getClauses());
		notAffectedClauses.removeAll(clauses);
		newSolver.addClauses(notAffectedClauses);
		for (final LiteralSet clause : clauses) {
			if ((clause.size() > 2) && isRedundant(newSolver, clause)) {
				newMig.removeClause(clause);
				redundantClauses.add(clause);
			} else {
				newSolver.addClause(clause);
			}
		}
	}

	private final boolean isRedundant(ISatSolver solver, LiteralSet curClause) {
		satCall++;
		return solver.hasSolution(curClause.negate()) == SatResult.FALSE;
	}

	public void setDetectStrong(boolean detectStrong) {
		this.detectStrong = detectStrong;
	}

	private void printNewMig() throws IOException {
		final FileWriter fw = new FileWriter("newMig.txt");
		final BufferedWriter bw = new BufferedWriter(fw);

		bw.write(newCNF.toString());
		bw.newLine();
		bw.write("MIG");
		bw.newLine();

		for (final Vertex ver : newMig.getAdjList()) {
			bw.write("vertex: " + ver.getVar());
			bw.write("  strong Edges: ");
			for (final int strongEdge : ver.getStrongEdges()) {
				bw.write(" " + strongEdge + " ");
			}
			bw.write("  weak Edges: ");
			for (final int weakEdge : ver.getComplexClauses()) {
				bw.write(" " + weakEdge + " ");
			}
			bw.newLine();
		}

		bw.close();
	}

	private void printCalculatedMig(ModalImplicationGraph testMig) throws IOException {
		final FileWriter fw = new FileWriter("testMig.txt");
		final BufferedWriter bw = new BufferedWriter(fw);

		bw.write(newCNF.toString());
		bw.newLine();
		bw.write("MIG");
		bw.newLine();

		for (final Vertex ver : testMig.getAdjList()) {
			bw.write("vertex: " + ver.getVar());
			bw.write("  strong Edges: ");
			for (final int strongEdge : ver.getStrongEdges()) {
				bw.write(" " + strongEdge + " ");
			}
			bw.write("  weak Edges: ");
			for (final int weakEdge : ver.getComplexClauses()) {
				bw.write(" " + weakEdge + " ");
			}
			bw.newLine();
		}

		bw.close();
	}

	private void printOldMig() throws IOException {
		final FileWriter fw = new FileWriter("oldMig.txt");
		final BufferedWriter bw = new BufferedWriter(fw);

		bw.write(oldCNF.toString());
		bw.newLine();
		bw.write("MIG");
		bw.newLine();

		for (final Vertex ver : oldMig.getAdjList()) {
			bw.write("vertex: " + ver.getVar());
			bw.write("  strong Edges: ");
			for (final int strongEdge : ver.getStrongEdges()) {
				bw.write(" " + strongEdge + " ");
			}
			bw.write("  weak Edges: ");
			for (final int weakEdge : ver.getComplexClauses()) {
				bw.write(" " + weakEdge + " ");
			}
			bw.newLine();
		}
		bw.close();
	}

	private void printTimes(long startTime, long removeTransStrongEdges, long deadCoreFeatures, long cleanCNF, long checkOldImplicitStrongEdges, long cnfDiff,
			long remClauses, long prevRedClauses, long newlyRedClauses, long addClauses, long completeDfsStrong, long completeDfsWeak,
			long completeImplicitStrong, long endTime, long endTimeOld, long startTimeOld, MIGBuilder testMigBuilder) throws IOException {
		final FileWriter fw_eval = new FileWriter("eval_time_automotive_complete_ohne_affected_redundant.csv", true);
		final BufferedWriter bw_eval = new BufferedWriter(fw_eval);
		final FileWriter fw_eval1 = new FileWriter("eval_time_automotive_complete_ohne_affected_redundant_adapted.txt", true);
		final BufferedWriter bw_eval1 = new BufferedWriter(fw_eval1);
		bw_eval1.write("remove transitive strong edges: " + (removeTransStrongEdges - startTime));
		bw_eval1.newLine();
		bw_eval1.write("calculated Core and Dead Features: " + (deadCoreFeatures - removeTransStrongEdges));
		bw_eval1.newLine();
		bw_eval1.write("clean CNF: " + (cleanCNF - deadCoreFeatures));
		bw_eval1.newLine();
		bw_eval1.write("check previously implicit strong edges: " + (checkOldImplicitStrongEdges - cleanCNF));
		bw_eval1.newLine();
		bw_eval1.write("calculate CNF difference: " + (cnfDiff - checkOldImplicitStrongEdges));
		bw_eval1.newLine();
		bw_eval1.write("removed Clauses: " + (remClauses - cnfDiff));
		bw_eval1.newLine();
		bw_eval1.write("checked preiously redundant Clauses of removed: " + (prevRedClauses - remClauses));
		bw_eval1.newLine();
		bw_eval1.write("checked newly redundant Clauses because of added: " + (newlyRedClauses - prevRedClauses));
		bw_eval1.newLine();
		bw_eval1.write("add Clauses: " + (addClauses - newlyRedClauses));
		bw_eval1.newLine();
		bw_eval1.write("detect transitive strong edges: " + (completeDfsStrong - addClauses));
		bw_eval1.newLine();
		bw_eval1.write("detect transitive weak edges: " + (completeDfsWeak - completeDfsStrong));
		bw_eval1.newLine();
		bw_eval1.write("detect implicit strong edges: " + (completeImplicitStrong - completeDfsWeak));
		bw_eval1.newLine();
		bw_eval1.write("detect transitive strong edges: " + (endTime - completeImplicitStrong));
		bw_eval1.newLine();
		bw_eval.write(dateiname);
		bw_eval.write(";" + (endTime - startTime));
		bw_eval.write(";" + (endTimeOld - startTimeOld));
		bw_eval.write(";" + (newMig.getImplicitStrongEdges().size()));
		bw_eval.write(";" + testMIG.getImplicitStrongEdges().size());
		bw_eval.write(";" + satCall);
		bw_eval.write(";" + testMigBuilder.getSatCalls());
		bw_eval.newLine();
		bw_eval.write("Zeitsparen durch incremental: " + (endTimeOld - startTimeOld - (endTime - startTime)));
		bw_eval.close();
		bw_eval1.close();
	}

	private void compare(ModalImplicationGraph adaptedMig, ModalImplicationGraph calculatedMig) throws IOException {
		final FileWriter fw_diff = new FileWriter("diff_eval_time_automotive_complete_ohne_affected_redundant.txt", true);
		final BufferedWriter bw_diff = new BufferedWriter(fw_diff);
		m: for (final LiteralSet literalSetAdaptedMig : adaptedMig.getComplexClauses()) {
			for (final LiteralSet literalSetCalculatedMig : calculatedMig.getComplexClauses()) {
				if (literalSetCalculatedMig.containsAll(literalSetAdaptedMig)) {
					continue m;
				}
			}
			bw_diff.write("LiteralSet kommt so nicht vor in berechnetem Mig: " + literalSetAdaptedMig.toString());
			bw_diff.newLine();
		}
		m: for (final LiteralSet literalSetCalculatedMig : calculatedMig.getComplexClauses()) {
			for (final LiteralSet literalSetAdaptedMig : adaptedMig.getComplexClauses()) {
				if (literalSetAdaptedMig.containsAll(literalSetCalculatedMig)) {
					continue m;
				}
			}
			bw_diff.write("LiteralSet kommt so nicht vor in adapted Mig: " + literalSetCalculatedMig.toString());
			bw_diff.newLine();
		}
		m: for (final Vertex vertexCalculatedMig : adaptedMig.getAdjList()) {
			for (final Vertex vertexSetAdaptedMig : calculatedMig.getAdjList()) {
				if (vertexCalculatedMig.getVar() == vertexSetAdaptedMig.getVar()) {
					continue m;
				}
			}
			System.out.println("Variable kommt so nicht vor in berechnetem Mig: " + vertexCalculatedMig.getVar());
		}
		m: for (final Vertex vertexSetAdaptedMig : calculatedMig.getAdjList()) {
			for (final Vertex vertexCalculatedMig : adaptedMig.getAdjList()) {
				if (vertexSetAdaptedMig.getVar() == vertexCalculatedMig.getVar()) {
					for (final int complClause : vertexSetAdaptedMig.getComplexClauses()) {
						for (final int complClauseCal : vertexCalculatedMig.getComplexClauses()) {
							for (final int complClauseLiteral : calculatedMig.getComplexClauses().get(complClause).getLiterals()) {
								for (final int complClauseCalLiteral : adaptedMig.getComplexClauses().get(complClauseCal).getLiterals()) {
									if (complClauseLiteral == complClauseCalLiteral) {
										continue m;
									}
								}
							}
							System.out.println("ist unterschiedlich");
						}
					}
					continue m;
				}
			}
			System.out.println("Variable kommt so nicht vor in adapted Mig: " + vertexSetAdaptedMig.getVar());
		}
		m: for (int i = 0; i < adaptedMig.getAdjList().size(); i++) {
			final int[] strongEdgesCalc = calculatedMig.getAdjList().get(i).getStrongEdges();
			final int[] strongEdgesAdapt = adaptedMig.getAdjList().get(i).getStrongEdges();
			if (strongEdgesAdapt.length != strongEdgesCalc.length) {
				bw_diff.write("Variablen an Stelle " + calculatedMig.getAdjList().get(i).getVar() + " haben unterschiedlich viele strong Edges");
				bw_diff.newLine();
				bw_diff.write("adapted Mig hat " + strongEdgesAdapt.length + " strong edges");
				bw_diff.newLine();
				bw_diff.write("calculated Mig hat " + strongEdgesCalc.length + " strong edges");
				bw_diff.newLine();
				bw_diff.newLine();
				continue m;
			}
			for (int j = 0; j < strongEdgesCalc.length; j++) {
				for (int strongEdge = 0; strongEdge < strongEdgesCalc.length; strongEdge++) {
					if (strongEdgesAdapt[j] == strongEdgesCalc[strongEdge]) {
						continue m;
					}
				}
				bw_diff.write("Variablen an Stelle" + i + "haben unterschiedliche strong Edges");
				bw_diff.newLine();
			}
		}
		for (int i = 0; i < adaptedMig.getAdjList().size(); i++) {
			if (adaptedMig.getAdjList().get(i).isCore()) {
				if (!calculatedMig.getAdjList().get(i).isCore()) {
					bw_diff.write("Variable an Stelle" + i + "ist core bei adaptedMig aber nicht bei calculated");
					bw_diff.newLine();
				}
			}
			if (adaptedMig.getAdjList().get(i).isDead()) {
				if (!calculatedMig.getAdjList().get(i).isDead()) {
					bw_diff.write("Variable an Stelle" + i + "ist dead bei adaptedMig aber nicht bei calculated");
					bw_diff.newLine();
				}
			}
			if (calculatedMig.getAdjList().get(i).isCore()) {
				if (!adaptedMig.getAdjList().get(i).isCore()) {
					bw_diff.write("Variable an Stelle" + i + "ist core bei calculated aber nicht bei adaptedMig");
					bw_diff.newLine();
				}
			}
			if (calculatedMig.getAdjList().get(i).isDead()) {
				if (!adaptedMig.getAdjList().get(i).isDead()) {
					bw_diff.write("Variable an Stelle" + i + "ist dead bei calculated aber nicht bei adaptedMig");
					bw_diff.newLine();
				}
			}

		}
		bw_diff.write("Insgesamt hat der adapted MIG " + adaptedMig.getImplicitStrongEdges().size() + " implicit strong edges und der calculated MIG "
			+ calculatedMig.getImplicitStrongEdges().size());
		bw_diff.write("ende");
		bw_diff.newLine();
		bw_diff.newLine();
		bw_diff.newLine();
		bw_diff.close();
	}

	private void printClauses() throws IOException {
		final FileWriter fw = new FileWriter("clauses.txt");
		final BufferedWriter bw = new BufferedWriter(fw);

		bw.write("oldCNF: ");
		bw.newLine();
		for (final LiteralSet literals : oldCNF.getClauses()) {
			for (final int literal : literals.getLiterals()) {
				bw.write(literal + ", ");
			}
			bw.write("<    >");
		}
		bw.newLine();
		bw.newLine();

		bw.write("newCNF: ");
		bw.newLine();
		for (final LiteralSet literals : newCNF.getClauses()) {
			for (final int literal : literals.getLiterals()) {
				bw.write(literal + ", ");
			}
			bw.write("<    >");
		}
		bw.newLine();
		bw.newLine();

		bw.write("newCNFclean: ");
		bw.newLine();
		for (final LiteralSet literals : newCNFclean.getClauses()) {
			for (final int literal : literals.getLiterals()) {
				bw.write(literal + ", ");
			}
			bw.write("<    >");
		}
		bw.newLine();
		bw.newLine();

		bw.write("addedClauses: ");
		bw.newLine();
		for (final LiteralSet literals : addedClauses) {
			for (final int literal : literals.getLiterals()) {
				bw.write(literal + ", ");
			}
			bw.write("<    >");
		}
		bw.newLine();
		bw.newLine();

		bw.write("removedClauses: ");
		bw.newLine();
		for (final LiteralSet literals : removedClauses) {
			for (final int literal : literals.getLiterals()) {
				bw.write(literal + ", ");
			}
			bw.write("<    >");
		}
		bw.newLine();
		bw.newLine();

		bw.close();
	}

	public static void installLibraries() {
		FMFactoryManager.getInstance().addExtension(DefaultFeatureModelFactory.getInstance());
		FMFactoryManager.getInstance().addExtension(MultiFeatureModelFactory.getInstance());
		FMFactoryManager.getInstance().setWorkspaceLoader(new CoreFactoryWorkspaceLoader());

		FMFormatManager.getInstance().addExtension(new XmlFeatureModelFormat());
		FMFormatManager.getInstance().addExtension(new SXFMFormat());

		ConfigurationFactoryManager.getInstance().addExtension(DefaultConfigurationFactory.getInstance());
		ConfigurationFactoryManager.getInstance().setWorkspaceLoader(new CoreFactoryWorkspaceLoader());
	}

}
