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
import java.util.Set;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
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
 * TODO description
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
	private Set<LiteralSet> removedClauses;
	private Set<LiteralSet> addedClauses;
	private Set<LiteralSet> redundantClauses;
	private ModalImplicationGraph newMig;
	private ModalImplicationGraph oldMig;
	private final int numberOfVariablesNew;
	private Set<Integer> affectedLiterals;
	private final byte[] dfsMark;
	final ArrayDeque<Integer> dfsStack = new ArrayDeque<>();

	public IncrementalMIGBuilder(CNF satInstance) {
		newCNF = satInstance;
		numberOfVariablesNew = satInstance.getVariables().size();
		dfsMark = new byte[numberOfVariablesNew];

	}

	public static void main(String[] args) throws Exception {
//		for (int i = 0; i < 20; i++) {
		installLibraries();
		final IFeatureModel fm = FeatureModelManager.load(Paths.get(
				"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\FeatureIDE\\FeatureIDE\\plugins\\de.ovgu.featureide.examples\\featureide_examples\\FeatureModels\\Automotive01\\model.xml"));
		final CNF newCnfPrep = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF().clone();
//		newCnfPrep.addClause(new LiteralSet(157, -63));
//		newCnfPrep.addClause(new LiteralSet(1589, -683, 56));
//		newCnfPrep.addClause(new LiteralSet(679, -2365, 1076));
//		newCnfPrep.getClauses().remove(10000);
		final IncrementalMIGBuilder incMigbuilder = new IncrementalMIGBuilder(newCnfPrep);
		incMigbuilder.buildPreconditions();
		incMigbuilder.execute(new NullMonitor<ModalImplicationGraph>());
//		}
	}

	private void buildPreconditions() {
		final IFeatureModel fm = FeatureModelManager.load(Paths.get(
				"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\FeatureIDE\\FeatureIDE\\plugins\\de.ovgu.featureide.examples\\featureide_examples\\FeatureModels\\Automotive01\\model.xml"));
		oldCNF = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF();
		final Set<String> allVariables = new HashSet<>(Arrays.asList(oldCNF.getVariables().getNames()).subList(1, oldCNF.getVariables().getNames().length));
		allVariables.addAll(Arrays.asList(newCNF.getVariables().getNames()).subList(1, newCNF.getVariables().getNames().length));
		final Variables variables = new Variables(allVariables);
		oldCNF = oldCNF.adapt(variables);
		newCNF = newCNF.adapt(variables);
		assert Objects.equals(oldCNF.getVariables(), newCNF.getVariables());
		final MIGBuilder migBuilder = new MIGBuilder(oldCNF);
		migBuilder.setCheckRedundancy(true);
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
		final Set<LiteralSet> notRedundantClauses = new HashSet<>(newCNF.getClauses());
		notRedundantClauses.removeAll(redundantClauses);
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));
		affectedLiterals = new HashSet<>();

		printOldMig();

		oldCNF.getClauses().forEach(c -> c.setOrder(LiteralSet.Order.NATURAL));
		newCNF.getClauses().forEach(c -> c.setOrder(LiteralSet.Order.NATURAL));

		// zeitzähler
		final long startTime = System.nanoTime();

		// calculate CNF difference
		calculateCNFDifference();

		final long cnfDiff = System.nanoTime() - startTime;

		// remove clauses from MIG
		for (final LiteralSet clause : removedClauses) {
			if (redundantClauses.contains(clause)) {
				redundantClauses.remove(clause);
				removedClauses.remove(clause);
			} else {
				newMig.removeClause(clause);
			}
		}

		final long remClauses = System.nanoTime() - cnfDiff - startTime;

		// handle previously redundant clauses
		if (!redundantClauses.isEmpty() && !removedClauses.isEmpty()) {
			affectedClauses =
				new HashSet<>(getThroughLiteralsAffectedClauses(new ArrayList<LiteralSet>(removedClauses), new ArrayList<LiteralSet>(redundantClauses)));
			handlePreviouslyRedundant(new ArrayList<>(affectedClauses));
		}

		final long prevRedClauses = System.nanoTime() - remClauses - cnfDiff - startTime;

		// handle newly redundant clauses
		if (!redundantClauses.isEmpty()) {
			notRedundantClauses.removeAll(redundantClauses);
		}
		affectedClauses =
			new HashSet<>(getThroughLiteralsAffectedClauses(new ArrayList<LiteralSet>(addedClauses), new ArrayList<LiteralSet>(notRedundantClauses)));
		handleNewlyRedundant(new ArrayList<>(affectedClauses));

		final long newlyRedClauses = System.nanoTime() - remClauses - prevRedClauses - cnfDiff - startTime;

		// handle core/dead features
		calculateDeadAndCoreFeatures();

		final long newlyDeadCoreFeatures = System.nanoTime() - newlyRedClauses - remClauses - prevRedClauses - cnfDiff - startTime;

		// TODO: Welche clauses müssen wegen nicht mehr core feature durch removed wieder hinzugefügt werden?
		for (final LiteralSet clause : addedClauses) {
			newMig.addClause(clause);
		}

		final long addClauses = System.nanoTime() - newlyDeadCoreFeatures - newlyRedClauses - remClauses - prevRedClauses - cnfDiff - startTime;

		detectStrong();

		// zeitzähler
		final long endTime = System.nanoTime();

		System.out.println("Benötigte Zeit beim incremental: " + (endTime - startTime));

		final long startTimeOld = System.nanoTime();

		final MIGBuilder migBuilder = new MIGBuilder(newCNF);
		ModalImplicationGraph testMIG = new ModalImplicationGraph();
		migBuilder.setCheckRedundancy(true);
		migBuilder.setDetectStrong(false);
		try {
			testMIG = migBuilder.execute(new NullMonitor<ModalImplicationGraph>());
		} catch (final Exception e) {
			e.printStackTrace();
		}

		final long endTimeOld = System.nanoTime();

		System.out.println("Benötigte Zeit beim neu Berechnen: " + (endTimeOld - startTimeOld));
		System.out.println("Zeitsparen durch incremental: " + (endTimeOld - startTimeOld - (endTime - startTime)));

		compare(newMig, testMIG);

		printTimes(startTime, cnfDiff, prevRedClauses, remClauses, newlyRedClauses, newlyDeadCoreFeatures, addClauses, endTime, endTimeOld, startTimeOld);

		printNewMig();

		return newMig;
	}

	private void calculateDeadAndCoreFeatures() {
		final ISatSolver solver = new AdvancedSatSolver(newCNF);
		solver.setSelectionStrategy(SelectionStrategy.POSITIVE);

	}

	private void mark() {
		for (int i = 0; i < dfsMark.length; i++) {
			dfsMark[i] &= 2;
		}
	}

	// TODO: Kann man da auch was sparen wegen evolution?
	private void detectStrong() {
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
		addedClauses = new HashSet<>(newCNF.getClauses());
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
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));
		final Set<LiteralSet> notAffectedClauses = new LinkedHashSet<>(newCNF.getClauses());
		notAffectedClauses.removeAll(clauses);
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
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));
		final Set<LiteralSet> notAffectedClauses = new LinkedHashSet<>(newCNF.getClauses());
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
		return solver.hasSolution(curClause.negate()) == SatResult.FALSE;
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

	private void printTimes(long startTime, long cnfDiff, long redClauses, long remClauses, long redClauses2, long newlyDeadCoreFeatures, long addClauses,
			long endTime, long endTimeOld, long startTimeOld) throws IOException {
		final FileWriter fw_eval = new FileWriter("eval_time_incomplete_nored_notrans.txt");
		final BufferedWriter bw_eval = new BufferedWriter(fw_eval);
		bw_eval.write("calculate CNF difference: " + cnfDiff);
		bw_eval.newLine();
		bw_eval.write("checked redundant Clauses of removed: " + redClauses);
		bw_eval.newLine();
		bw_eval.write("removed Clauses: " + remClauses);
		bw_eval.newLine();
		bw_eval.write("checked redundant Clauses of added: " + redClauses2);
		bw_eval.newLine();
		bw_eval.write("checked newly Core and Dead Features: " + newlyDeadCoreFeatures);
		bw_eval.newLine();
		bw_eval.write("add Clauses: " + addClauses);
		bw_eval.newLine();
		bw_eval.write("detect transitive strong edges: " + (endTime - redClauses2 - remClauses - redClauses - cnfDiff - startTime - newlyDeadCoreFeatures));
		bw_eval.newLine();
		bw_eval.write("Benötigte Zeit beim incremental: " + (endTime - startTime));
		bw_eval.newLine();
		bw_eval.write("Benötigte Zeit beim neu Berechnen: " + (endTimeOld - startTimeOld));
		bw_eval.newLine();
		bw_eval.write("Zeitsparen durch incremental: " + (endTimeOld - startTimeOld - (endTime - startTime)));
		bw_eval.close();
	}

	private void compare(ModalImplicationGraph adaptedMig, ModalImplicationGraph calculatedMig) throws IOException {
		final FileWriter fw_diff = new FileWriter("diff.txt");
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
				for (final int literal : literalSetCalculatedMig.getLiterals()) {
					if (literalSetAdaptedMig.containsLiteral(literal)) {
						continue m;
					}
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
		m: for (final Vertex vertexSetAdaptedMig : adaptedMig.getAdjList()) {
			for (final Vertex vertexCalculatedMig : calculatedMig.getAdjList()) {
				if (vertexSetAdaptedMig.getVar() == vertexCalculatedMig.getVar()) {
					continue m;
				}
			}
			System.out.println("Variable kommt so nicht vor in berechnetem Mig: " + vertexSetAdaptedMig.getVar());
		}
		bw_diff.close();
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
