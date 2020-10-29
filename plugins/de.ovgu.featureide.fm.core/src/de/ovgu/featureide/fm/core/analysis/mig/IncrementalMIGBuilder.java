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

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util.Pair;
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
	private List<LiteralSet> removedClauses;
	private List<LiteralSet> added;
	private List<LiteralSet> redundantClauses;
	private ModalImplicationGraph newMig;
	private ModalImplicationGraph oldMig;
	private final int numberOfVariablesNew;
	private AdjMatrix adjMatrix;

	public IncrementalMIGBuilder(CNF satInstance) {
		newCNF = satInstance;
		numberOfVariablesNew = satInstance.getVariables().size();
	}

	public static void main(String[] args) throws Exception {
		installLibraries();
		final IFeatureModel fm = FeatureModelManager.load(Paths.get(
				"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\FeatureIDE\\FeatureIDE\\plugins\\de.ovgu.featureide.examples\\featureide_examples\\FeatureModels\\Automotive01\\model.xml"));

		final CNF newCnfPrep = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF().clone();
		newCnfPrep.getClauses().remove(700);
		final IncrementalMIGBuilder incMigbuilder = new IncrementalMIGBuilder(newCnfPrep);
		incMigbuilder.buildPreconditions();
//		for (int i = 0; i < 10; i++) {
		incMigbuilder.execute(new NullMonitor<ModalImplicationGraph>());
//		}
	}

	/**
	 *
	 */
	private void buildPreconditions() {
		final IFeatureModel fm = FeatureModelManager.load(Paths.get(
				"C:\\Users\\rahel\\OneDrive\\Dokumente\\Uni\\Bachelorarbeit\\FeatureIDE\\FeatureIDE\\plugins\\de.ovgu.featureide.examples\\featureide_examples\\FeatureModels\\Automotive01\\model.xml"));

		oldCNF = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF();
		final MIGBuilder migBuilder = new MIGBuilder(oldCNF);
		oldMig = LongRunningWrapper.runMethod(migBuilder);
		redundantClauses = migBuilder.getRedundantClauses();
		adjMatrix = new AdjMatrix(numberOfVariablesNew);
		newMig = new ModalImplicationGraph(declareMigSize(oldCNF.getVariables().size(), numberOfVariablesNew) * 2);
		newMig.copyValues(oldMig); // gleich anmerken das doof
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

	public int declareMigSize(int numberOfVariablesOld, int numberOfVariablesNew) {
		return numberOfVariablesNew > numberOfVariablesOld ? numberOfVariablesNew : numberOfVariablesOld;
	}

	@Override
	public ModalImplicationGraph execute(IMonitor<ModalImplicationGraph> monitor) throws Exception {
//		System.out.println(oldCNF.toString());
//		System.out.println("MIG");
//		for (final Vertex ver : oldMig.getAdjList()) {
//			System.out.print("vertex: " + ver.getVar());
//			System.out.print("  strong Edges: ");
//			for (final int strongEdge : ver.getStrongEdges()) {
//				System.out.print(" " + strongEdge + " ");
//			}
//			System.out.print("  weak Edges: ");
//			for (final int weakEdge : ver.getComplexClauses()) {
//				System.out.print(" " + weakEdge + " ");
//			}
//			System.out.println();
//		}

		// zeitzähler
		final long startTime = System.nanoTime();

		final Pair<List<LiteralSet>, List<LiteralSet>> difference = calculateCNFDifference();
		final List<LiteralSet> removed = difference.getKey();
		List<LiteralSet> affectedClauses = new ArrayList<>();
		System.out.println(System.nanoTime() - startTime);
		if (!redundantClauses.isEmpty()) {
			removed.removeAll(redundantClauses);
			affectedClauses = getAllAffectedClauses(removed, redundantClauses);
			handlePreviouslyRedundant(affectedClauses);
		}
		for (final LiteralSet clause : removed) {
			newMig.removeClause(clause);
		}
		System.out.println(System.nanoTime() - startTime);

		final List<LiteralSet> added = difference.getValue();
		final List<LiteralSet> notRedundantClauses = newCNF.getClauses().clone();
		if (redundantClauses != null) {
			notRedundantClauses.removeAll(redundantClauses);
		}
		System.out.println(System.nanoTime() - startTime);

		affectedClauses = getAllAffectedClauses(added, notRedundantClauses);
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));
		for (final LiteralSet clause : added) {
			if ((clause.size() < 3) || !isRedundant(newSolver, clause)) {
				newMig.addClause(clause);
			} else {
				redundantClauses.add(clause);
			}
		}

		// zeitzähler
		final long endTime = System.nanoTime();

		System.out.println("Benötigte Zeit beim incremental: " + (endTime - startTime));

		final long startTimeOld = System.nanoTime();

		final MIGBuilder migBuilder = new MIGBuilder(newCNF);
		ModalImplicationGraph testMIG = new ModalImplicationGraph();
		migBuilder.setDetectStrong(false);
		try {
			testMIG = migBuilder.execute(new NullMonitor<ModalImplicationGraph>());
		} catch (final Exception e) {
			e.printStackTrace();
		}

		final long endTimeOld = System.nanoTime();

		System.out.println("Benötigte Zeit beim neu Berechnen: " + (endTimeOld - startTimeOld));

		System.out.println();
		compare(newMig, testMIG);

//		System.out.println(newCNF.toString());
//		System.out.println("MIG");
//		for (final Vertex ver : newMig.getAdjList()) {
//			System.out.print("vertex: " + ver.getVar());
//			System.out.print("  strong Edges: ");
//			for (final int strongEdge : ver.getStrongEdges()) {
//				System.out.print(" " + strongEdge + " ");
//			}
//			System.out.print("  weak Edges: ");
//			for (final int weakEdge : ver.getComplexClauses()) {
//				System.out.print(" " + weakEdge + " ");
//			}
//			System.out.println();
//		}
		return newMig;
	}

	// TODO: IMPROVE!!!!!! Much too takes long!!!!!
	public Pair<List<LiteralSet>, List<LiteralSet>> calculateCNFDifference() {
		removedClauses = oldCNF.getClauses().clone();
		removedClauses.removeAll(newCNF.getClauses());
		added = newCNF.getClauses().clone();
		added.removeAll(oldCNF.getClauses());
		return new Pair<>(removedClauses, added);
	}

	public List<LiteralSet> getAllAffectedClauses(List<LiteralSet> startClauses, List<LiteralSet> possiblyAffectedClauses) {
		final List<LiteralSet> affectedClauses = new ArrayList<>();
		for (final LiteralSet startClause : startClauses) {
			clauseList: for (final LiteralSet clause : possiblyAffectedClauses) {
				for (final int literal : clause.getLiterals()) {
					if (startClause.containsLiteral(literal)) {
						affectedClauses.add(clause);
						continue clauseList;
					}
				}
			}
		}
		return affectedClauses;
	}

	public void handlePreviouslyRedundant(List<LiteralSet> clauses) {
		final AdvancedSatSolver newSolver = new AdvancedSatSolver(new CNF(newCNF, false));
		for (final LiteralSet clause : clauses) {
			if (!isRedundant(newSolver, clause)) {
				newMig.addClause(clause);
				redundantClauses.remove(clause);
			}
		}
	}

	public void handleNewlyRedundant(List<LiteralSet> clauses) {
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

	private void compare(ModalImplicationGraph adaptedMig, ModalImplicationGraph calculatedMig) {
		m: for (final LiteralSet literalSetAdaptedMig : adaptedMig.getComplexClauses()) {
			for (final LiteralSet literalSetCalculatedMig : calculatedMig.getComplexClauses()) {
				for (final int literal : literalSetAdaptedMig.getLiterals()) {
					if (literalSetCalculatedMig.containsLiteral(literal)) {
						continue m;
					}
				}
			}
			System.out.println("LiteralSet kommt so nicht vor in berechnetem Mig: " + literalSetAdaptedMig.getLiterals());
		}
		m: for (final LiteralSet literalSetCalculatedMig : adaptedMig.getComplexClauses()) {
			for (final LiteralSet literalSetAdaptedMig : calculatedMig.getComplexClauses()) {
				for (final int literal : literalSetCalculatedMig.getLiterals()) {
					if (literalSetAdaptedMig.containsLiteral(literal)) {
						continue m;
					}
				}
			}
			System.out.println("LiteralSet kommt so nicht vor in adapted Mig: " + literalSetCalculatedMig.getLiterals());
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

}
