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
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
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

	private CNF oldCNF;
	private final CNF newCNF;
	private Set<LiteralSet> removedClauses;
	private Set<LiteralSet> addedClauses;
	private Set<LiteralSet> redundantClauses;
	private ModalImplicationGraph newMig;
	private ModalImplicationGraph oldMig;
	private final int numberOfVariablesNew;
	private Set<Integer> affectedLiterals;

	public IncrementalMIGBuilder(CNF satInstance) {
		newCNF = satInstance;
		numberOfVariablesNew = satInstance.getVariables().size();
	}

	public static void main(String[] args) throws Exception {
		for (int i = 0; i < 20; i++) {
			installLibraries();
			final IFeatureModel fm = FeatureModelManager.load(Paths.get(
					"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\busybox_modelle_entpackt\\2007-05-20_17-12-43\\\\2007-05-20_17-12-43\\model.xml"));
			final CNF newCnfPrep = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF().clone();
			newCnfPrep.addClause(new LiteralSet(109));
			final IncrementalMIGBuilder incMigbuilder = new IncrementalMIGBuilder(newCnfPrep);
			incMigbuilder.buildPreconditions();
			incMigbuilder.execute(new NullMonitor<ModalImplicationGraph>());
		}
	}

	private void buildPreconditions() {
		final IFeatureModel fm = FeatureModelManager.load(Paths.get(
				"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\busybox_modelle_entpackt\\2007-05-20_17-12-43\\2007-05-20_17-12-43\\model.xml"));
		oldCNF = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF();
		final MIGBuilder migBuilder = new MIGBuilder(oldCNF);
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
		final Set<LiteralSet> notRedundantClauses = new HashSet<>(newCNF.getClauses().clone());
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));

		printOldMig();

		// zeitzähler
		final long startTime = System.nanoTime();

		// calculate CNF difference
		calculateCNFDifference();

		final long cnfDiff = System.nanoTime() - startTime;

		// remove clauses from MIG
		removedClauses.removeAll(redundantClauses);
		for (final LiteralSet clause : removedClauses) {
			newMig.removeClause(clause);
		}

		final long remClauses = System.nanoTime() - cnfDiff - startTime;

		affectedClauses = new HashSet<>(getAllAffectedClauses(new ArrayList<LiteralSet>(removedClauses), newCNF.getClauses()));

		// handle previously redundant clauses
		// TODO: redundantClauses in MIGBuilder abspeichern
		if (!redundantClauses.isEmpty()) {
			handlePreviouslyRedundant(affectedClauses);
		}

		// handle previously core/dead features
		// TODO: müssen jetzt Kanten zum MIG hinzugefügt werden (da sie wegen dem core/dead feature am anfang nicht hinzugefügt wurden)?
		for (final int variable : affectedLiterals) {
			if (oldMig.getVertex(variable).isCore()) {
				newSolver.assignmentPush(-variable);
				if (newSolver.hasSolution() == SatResult.TRUE) {
					newMig.getVertex(variable).setCore(false);
					newMig.getVertex(-variable).setDead(false);
				}
			} else if (oldMig.getVertex(variable).isDead()) {
				newSolver.assignmentPush(-variable);
				if (newSolver.hasSolution() == SatResult.TRUE) {
					newMig.getVertex(variable).setDead(false);
					newMig.getVertex(-variable).setCore(false);
				}
			}
		}

		final long prevRedClauses = System.nanoTime() - remClauses - cnfDiff - startTime;

		// handle newly redundant clauses
		if (!redundantClauses.isEmpty()) {
			notRedundantClauses.removeAll(redundantClauses);
		}
		affectedClauses = new HashSet<>(getAllAffectedClauses(new ArrayList<LiteralSet>(addedClauses), new ArrayList<LiteralSet>(notRedundantClauses)));
		handleNewlyRedundant(affectedClauses);

		final long newlyRedClauses = System.nanoTime() - remClauses - prevRedClauses - cnfDiff - startTime;

		// handle newly core/dead features
		// TODO: affectedLiterals: removeAll die schon bei affected überprüft wurden
		// TODO: remove from added
		for (final int variable : affectedLiterals) {
			if (!oldMig.getVertex(variable).isCore() && !oldMig.getVertex(variable).isDead()) {
				newSolver.assignmentPush(-variable);
				if (newSolver.hasSolution() == SatResult.FALSE) {
					// MACH DIR DARÜBER VERNÜNFTIG GEDANKEN
				}
			}
		}

		for (final LiteralSet clause : addedClauses) {
			newMig.addClause(clause);
		}

		// zeitzähler
		final long endTime = System.nanoTime();

		System.out.println();
		System.out.println();

		System.out.println("Benötigte Zeit beim incremental: " + (endTime - startTime));

		final long startTimeOld = System.nanoTime();

		final MIGBuilder migBuilder = new MIGBuilder(newCNF);
		ModalImplicationGraph testMIG = new ModalImplicationGraph();
		// migBuilder.setCheckRedundancy(true);
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

		printTimes(startTime, cnfDiff, prevRedClauses, remClauses, newlyRedClauses, endTime, endTimeOld, startTimeOld);

		printNewMig();

		return newMig;
	}

	public void calculateCNFDifference() {
		removedClauses = new HashSet<>(oldCNF.getClauses());
		removedClauses.removeAll(newCNF.getClauses());
		addedClauses = new HashSet<>(newCNF.getClauses());
		addedClauses.removeAll(oldCNF.getClauses());
	}

	public List<LiteralSet> getAllAffectedClauses(List<LiteralSet> startClauses, List<LiteralSet> possiblyAffectedClauses) {
		affectedLiterals = new HashSet<>();
		final List<LiteralSet> affectedClauses = new ArrayList<>();
		for (final LiteralSet startClause : startClauses) {
			clauseList: for (int i = 0; i < possiblyAffectedClauses.size(); i++) {
				for (final int variable : startClause.getLiterals()) {
					if (possiblyAffectedClauses.get(i).getVariables().containsVariable(Math.abs(variable))) {
						affectedClauses.add(possiblyAffectedClauses.get(i));
						for (final int literal : possiblyAffectedClauses.get(i).getLiterals()) {
							affectedLiterals.add(Math.abs(literal));
						}
						possiblyAffectedClauses.remove(i);
						i--;
						continue clauseList;
					}

				}
			}
		}
		if (!affectedClauses.isEmpty()) {
			affectedClauses.addAll(getAllAffectedClauses(affectedClauses, possiblyAffectedClauses));
		}
		return affectedClauses;

	}

	public void handlePreviouslyRedundant(Set<LiteralSet> clauses) {
		// Sat Solver oben nur einmal erzeugen und in beiden Methoden verwenden
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));
		for (final LiteralSet clause : clauses) {
			if (!isRedundant(newSolver, clause)) {
				newMig.addClause(clause);
				redundantClauses.remove(clause);
			}
		}
	}

	public void handleNewlyRedundant(Set<LiteralSet> clauses) {
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));
		for (final LiteralSet clause : clauses) {
			if ((clause.size() > 2) && isRedundant(newSolver, clause)) {
				newMig.removeClause(clause);
				redundantClauses.add(clause);
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

	private void printTimes(long startTime, long cnfDiff, long redClauses, long remClauses, long redClauses2, long endTime, long endTimeOld, long startTimeOld)
			throws IOException {
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
		bw_eval.write("add clauses: " + (endTime - redClauses2 - remClauses - redClauses - cnfDiff - startTime));
		bw_eval.newLine();
		bw_eval.write("Benötigte Zeit beim incremental: " + (endTime - startTime));
		bw_eval.newLine();
		bw_eval.write("Benötigte Zeit beim neu Berechnen: " + (endTimeOld - startTimeOld));
		bw_eval.newLine();
		bw_eval.write("Zeitsparen durch incremental: " + (endTimeOld - startTimeOld - (endTime - startTime)));
		bw_eval.close();
	}

	private void compare(ModalImplicationGraph adaptedMig, ModalImplicationGraph calculatedMig) {
		m: for (final LiteralSet literalSetAdaptedMig : adaptedMig.getComplexClauses()) {
			for (final LiteralSet literalSetCalculatedMig : calculatedMig.getComplexClauses()) {
				if (literalSetCalculatedMig.containsAll(literalSetAdaptedMig)) {
					continue m;
				}
			}
			System.out.println("LiteralSet kommt so nicht vor in berechnetem Mig: " + literalSetAdaptedMig.toString());
		}
		m: for (final LiteralSet literalSetCalculatedMig : calculatedMig.getComplexClauses()) {
			for (final LiteralSet literalSetAdaptedMig : adaptedMig.getComplexClauses()) {
				for (final int literal : literalSetCalculatedMig.getLiterals()) {
					if (literalSetAdaptedMig.containsLiteral(literal)) {
						continue m;
					}
				}
			}
			System.out.println("LiteralSet kommt so nicht vor in adapted Mig: " + literalSetCalculatedMig.toString());
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
