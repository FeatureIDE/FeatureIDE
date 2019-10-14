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
package org.prop4j.analyses.impl.general.evaluation;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.prop4j.analyses.impl.general.sat.ClearCoreDeadAnalysis;
import org.prop4j.analyses.impl.general.sat.ClearImplicationAnalysis;
import org.prop4j.analyses.impl.general.sat.CoreDeadAnalysis;
import org.prop4j.analyses.impl.general.sat.CountSolutionsAnalysis;
import org.prop4j.analyses.impl.general.sat.HasSolutionAnalysis;
import org.prop4j.analyses.impl.general.sat.ImplicationAnalysis;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solver.impl.sat4j.Sat4JSatSolverFactory;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolverFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.IndependentRedundancyAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.filter.OptionalFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * A collection of methods for working with {@link IFeatureModel} will replace the corresponding methods in {@link IFeatureModel}
 *
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class EvaluatedFeatureModelAnaysis {

	public static List<EvaluationEntry> validAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> cleanCoreDeadAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> optiCoreDeadAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> cleanFalseOptionalAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> optiFalseOptionalAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> countSolutions = new ArrayList<>();
	public static List<EvaluationEntry> tautologicalConstraints = new ArrayList<>();
	public static List<EvaluationEntry> redundantConstraints = new ArrayList<>();

	public static void printResult() {
		printResultHidden("Valid", validAnalysis);
		printResultHidden("CleanCoreDead", cleanCoreDeadAnalysis);
		printResultHidden("OptiCoreDead", optiCoreDeadAnalysis);
		printResultHidden("CleanFalseOptional", cleanFalseOptionalAnalysis);
		printResultHidden("OptiFalseOptional", optiFalseOptionalAnalysis);
		printResultHidden("CountSolutions", countSolutions);
//		printResultHidden("TautologicalConstraints", tautologicalConstraints);
		printResultHidden("RedundantConstraints", redundantConstraints);
	}

	private static void printResultHidden(String filename, List<EvaluationEntry> entryList) {
		final String filetowrite = "C:\\Users\\Joshua\\Desktop\\Uni\\SS 19\\Projektarbeit\\Data\\" + filename + ".txt";
		try (FileWriter fw = new FileWriter(filetowrite)) {
			fw.write(
					"Model;AnzahlFeatures;AnzahlConstraints;AnzahlKlauseln;Sat4J - Init;Sat4J - SolverTime;Sat4J - GesamtAnalyse;SMTInterpol - Init;SMTInterpol - SolveTime;SMTInterpol - GesamtAnalyse;Native - Init;Native - SolverTime;Native - GesamtAnalyse;Result - Overview;Sat4J - Result;SMTInterpol - Result;Native - Result\n");
			for (final EvaluationEntry evaluationEntry : entryList) {
				fw.write(evaluationEntry.toString() + "\n");
			}
		} catch (final IOException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private final IFeatureModel fm;
	private final AdvancedNodeCreator nodeCreator;
	protected de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver sat4jNativeSolver;
	protected ISatSolver sat4jSolverFull;
	protected ISatSolver sat4jSolverStructure;
	protected ISatSolver sat4jSolverConstraints;
	protected ISatSolver smtInterpolSolverFull;
	protected ISatSolver smtInterpolSolverStrucutre;
	protected ISatSolver smtInterpolSolverConstraints;

	public EvaluatedFeatureModelAnaysis(IFeatureModel fm) {
		this.fm = fm;

		// Setup problem
		nodeCreator = new AdvancedNodeCreator(fm);
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		nodeCreator.setUseOldNames(false);

		// Only create the cnf one time for every mode
		nodeCreator.setModelType(ModelType.All);
		final ISatProblem allModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		nodeCreator.setModelType(ModelType.OnlyStructure);
		final ISatProblem structureModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		nodeCreator.setModelType(ModelType.OnlyConstraints);
		final ISatProblem constraintModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));

		// Setup Sat4J Solvers
		final Sat4JSatSolverFactory sat4JFactory = new Sat4JSatSolverFactory();
		sat4jSolverFull = sat4JFactory.getAnalysisSolver(allModelProblem);
		sat4jSolverStructure = sat4JFactory.getAnalysisSolver(structureModelProblem);
		sat4jSolverConstraints = sat4JFactory.getAnalysisSolver(constraintModelProblem);

		// Setup JavaSMT Solver
		smtInterpolSolverFull = new JavaSmtSatSolverFactory(Solvers.SMTINTERPOL).getAnalysisSolver(allModelProblem);
		smtInterpolSolverStrucutre = new JavaSmtSatSolverFactory(Solvers.SMTINTERPOL).getAnalysisSolver(structureModelProblem);
		smtInterpolSolverConstraints = new JavaSmtSatSolverFactory(Solvers.SMTINTERPOL).getAnalysisSolver(constraintModelProblem);

		// Setup Native Solver (SAT4J)
		final CNF cnf = FeatureModelManager.getInstance(fm).getPersistentFormula().getCNF();
		sat4jNativeSolver = new AdvancedSatSolver(cnf);

		for (int i = 0; i < 1; i++) {
			doMagic();
		}
	}

	private void checkCleanFeatureDead(EvaluationEntry entry, ISatSolver solver) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final ClearCoreDeadAnalysis analysis = new ClearCoreDeadAnalysis(solver);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final LiteralSet result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		final List<String> featureNamesCore = new ArrayList<>();
		final List<String> featureNamesDead = new ArrayList<>();
		for (final int iResult : result.getLiterals()) {
			if (iResult >= 0) {
				featureNamesCore.add("" + solver.getProblem().getVariableOfIndex(iResult));
			} else {
				featureNamesDead.add("" + solver.getProblem().getVariableOfIndex(iResult));
			}
		}

		Collections.sort(featureNamesCore);
		Collections.sort(featureNamesDead);
		entry.results.add("Core:" + featureNamesCore + " Dead:" + featureNamesDead);

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	private void checkCleanFeatureFO(EvaluationEntry entry, ISatSolver solver, List<int[]> pairs) {

		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final ClearImplicationAnalysis analysis = new ClearImplicationAnalysis(solver, pairs);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final List<int[]> result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		final List<String> featureNamesFO = new ArrayList<>();
		for (final int[] iResult : result) {
			for (int i = 0; i < iResult.length; i++) {
				final int feature = iResult[i];
				if (feature >= 0) {
					// Is Fo Feature
					featureNamesFO.add("" + solver.getProblem().getVariableOfIndex(feature));
				}
			}
		}

		Collections.sort(featureNamesFO);
		entry.results.add("False-Optional:" + featureNamesFO);

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	private void checkFeatureDead(EvaluationEntry entry, ISatSolver solver) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final CoreDeadAnalysis analysis = new CoreDeadAnalysis(solver);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final LiteralSet result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		final List<String> featureNamesCore = new ArrayList<>();
		final List<String> featureNamesDead = new ArrayList<>();
		for (final int iResult : result.getLiterals()) {
			if (iResult >= 0) {
				featureNamesCore.add("" + solver.getProblem().getVariableOfIndex(iResult));
			} else {
				featureNamesDead.add("" + solver.getProblem().getVariableOfIndex(iResult));
			}
		}

		Collections.sort(featureNamesCore);
		Collections.sort(featureNamesDead);
		entry.results.add("Core:" + featureNamesCore + " Dead:" + featureNamesDead);

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	private void checkFeatureDeadNative(EvaluationEntry entry, de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver solver) {

		// Add sebastian native approach
		long t1 = System.currentTimeMillis();
		final de.ovgu.featureide.fm.core.analysis.cnf.analysis.CoreDeadAnalysis analysis =
			new de.ovgu.featureide.fm.core.analysis.cnf.analysis.CoreDeadAnalysis(solver);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final LiteralSet result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		final List<String> featureNamesCore = new ArrayList<>();
		final List<String> featureNamesDead = new ArrayList<>();
		for (final int iResult : result.getLiterals()) {
			if (iResult >= 0) {
				featureNamesCore.add("" + solver.getSatInstance().getVariables().getName(iResult));
			} else {
				featureNamesDead.add("" + solver.getSatInstance().getVariables().getName(iResult));
			}
		}

		Collections.sort(featureNamesCore);
		Collections.sort(featureNamesDead);
		entry.results.add("Core:" + featureNamesCore + " Dead:" + featureNamesDead);

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	private void checkFeatureFO(EvaluationEntry entry, ISatSolver solver, List<int[]> pairs) {

		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final ImplicationAnalysis analysis = new ImplicationAnalysis(solver, pairs);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final List<int[]> result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		final List<String> featureNamesFO = new ArrayList<>();
		for (final int[] iResult : result) {
			for (int i = 0; i < iResult.length; i++) {
				final int feature = iResult[i];
				if (feature >= 0) {
					// Is Fo Feature
					featureNamesFO.add("" + solver.getProblem().getVariableOfIndex(feature));
				}
			}
		}

		Collections.sort(featureNamesFO);
		entry.results.add("False-Optional:" + featureNamesFO);

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	/**
	 * @param entry
	 * @param sat4jNativeSolver2
	 */
	private void checkFeatureFONative(EvaluationEntry entry, de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver sat4jNativeSolver2,
			List<LiteralSet> foClauses) {
		// Add sebastian native approach
		long t1 = System.currentTimeMillis();
		final IndependentRedundancyAnalysis analysis = new IndependentRedundancyAnalysis(sat4jNativeSolver2);
		analysis.setClauseList(foClauses);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final List<LiteralSet> result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		// Count found FO Features
		final List<String> featureNamesFO = new ArrayList<>();
		for (final LiteralSet literalSet : result) {
			if (literalSet != null) {
				for (int i = 0; i < literalSet.getLiterals().length; i++) {
					final int feature = literalSet.getLiterals()[i];
					if (feature >= 0) {
						// Is Fo Feature
						featureNamesFO.add("" + sat4jNativeSolver2.getSatInstance().getVariables().getName(feature));
					}
				}
			}
		}

		Collections.sort(featureNamesFO);
		entry.results.add("False-Optional:" + featureNamesFO);

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);

	}

	private void checkVoid(EvaluationEntry entry, ISatSolver solver) {
		// Add sebastian native approach
		long t1 = System.currentTimeMillis();
		final HasSolutionAnalysis analysis = new HasSolutionAnalysis(solver);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final Boolean result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		entry.results.add("[" + result + "]");

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	private void checkVoidNative(EvaluationEntry entry, de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver solver) {
		// Add sebastian native approach
		long t1 = System.currentTimeMillis();
		final de.ovgu.featureide.fm.core.analysis.cnf.analysis.HasSolutionAnalysis analysis =
			new de.ovgu.featureide.fm.core.analysis.cnf.analysis.HasSolutionAnalysis(solver);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final Boolean result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		entry.results.add("[" + result + "]");

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	private void doMagic() {
		final String modelName = fm.getSourceFile().getName(fm.getSourceFile().getNameCount() - 1).toString();

		// Void Model
		evaluateVoidAnalysis(modelName);

		// Core and Dead Features
		evaluateClearCoreDead(modelName);
		evaluateOptiCoreDead(modelName);

		// False-Optional Features
		evaluateClearFOFeatures(modelName);
		evaluateOptiFOFeatures(modelName);

		// Redundant constraints
		evaluateRedundantCostraints(modelName);

		// Count Solutions
		evaluateCountSolutionsAnalysis(modelName);

		// Save and write the results to a file
		printResult();
	}

	private void evaluateRedundantCostraints(String modelName) {
		final EvaluationEntry entry =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), sat4jSolverFull.getProblem().getClauseCount(), modelName);

		// checkRedundantConstraints(entry, sat4jSolverFull);
		// checkRedundantConstraints(entry, smtInterpolSolverFull);
		checkRedundantConstraintsNative(entry, sat4jNativeSolver);

		redundantConstraints.add(entry);
	}

	private void checkRedundantConstraintsNative(EvaluationEntry entry,
			de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver sat4jNativeSolver) {
		// Add sebastians native approach
		long t1 = System.currentTimeMillis();
		// Setup clauses

		final de.ovgu.featureide.fm.core.analysis.cnf.analysis.RedundancyAnalysis analysis =
			new de.ovgu.featureide.fm.core.analysis.cnf.analysis.RedundancyAnalysis(sat4jNativeSolver);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final List<LiteralSet> result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		entry.results.add("[" + result + "]");

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	private void evaluateClearCoreDead(String modelName) {
		final EvaluationEntry entry =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), sat4jSolverFull.getProblem().getClauseCount(), modelName);

		checkCleanFeatureDead(entry, sat4jSolverFull);
		checkCleanFeatureDead(entry, smtInterpolSolverFull);
		checkFeatureDeadNative(entry, sat4jNativeSolver);

		cleanCoreDeadAnalysis.add(entry);
	}

	private void evaluateClearFOFeatures(String modelName) {
		final EvaluationEntry entry =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), sat4jSolverFull.getProblem().getClauseCount(), modelName);

		final List<IFeature> poFOFeature = Functional.filterToList(fm.getFeatures(), new OptionalFeatureFilter());
		final List<int[]> possibleFOFeatures = new ArrayList<>();
		final List<LiteralSet> possibleFOFeaturesSeb = new ArrayList<>();
		for (final IFeature iFeature : poFOFeature) {
			// Get parent
			if (iFeature.getStructure().getParent() != null) {
				final IFeature iParent = iFeature.getStructure().getParent().getFeature();
				int indexFeature = sat4jSolverFull.getProblem().getIndexOfVariable(iFeature.getName());
				int indexParent = sat4jSolverFull.getProblem().getIndexOfVariable(iParent.getName());
				final int[] pair = { -indexParent, indexFeature };
				// Result : {-Parent, Possible FO Feature}
				possibleFOFeatures.add(pair);

				// Nativ
				indexFeature = sat4jNativeSolver.getSatInstance().getVariables().getVariable(iFeature.getName(), true);
				indexParent = sat4jNativeSolver.getSatInstance().getVariables().getVariable(iParent.getName(), false);
				// Result : {Parent, Possible FO Feature} because already signed above
				possibleFOFeaturesSeb.add(new LiteralSet(indexParent, indexFeature));
			}
		}

		checkCleanFeatureFO(entry, sat4jSolverFull, possibleFOFeatures);
		checkCleanFeatureFO(entry, smtInterpolSolverFull, possibleFOFeatures);
		checkFeatureFONative(entry, sat4jNativeSolver, possibleFOFeaturesSeb);

		cleanFalseOptionalAnalysis.add(entry);
	}

	private void evaluateOptiCoreDead(String modelName) {
		final EvaluationEntry entry =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), sat4jSolverFull.getProblem().getClauseCount(), modelName);

		checkFeatureDead(entry, sat4jSolverFull);
		checkFeatureDead(entry, smtInterpolSolverFull);
		checkFeatureDeadNative(entry, sat4jNativeSolver);

		optiCoreDeadAnalysis.add(entry);
	}

	private void evaluateOptiFOFeatures(String modelName) {
		final EvaluationEntry entry =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), sat4jSolverFull.getProblem().getClauseCount(), modelName);

		final List<IFeature> poFOFeature = Functional.filterToList(fm.getFeatures(), new OptionalFeatureFilter());
		final List<int[]> possibleFOFeatures = new ArrayList<>();
		final List<LiteralSet> possibleFOFeaturesSeb = new ArrayList<>();
		for (final IFeature iFeature : poFOFeature) {
			// Get parent
			if (iFeature.getStructure().getParent() != null) {
				final IFeature iParent = iFeature.getStructure().getParent().getFeature();
				int indexFeature = sat4jSolverFull.getProblem().getIndexOfVariable(iFeature.getName());
				int indexParent = sat4jSolverFull.getProblem().getIndexOfVariable(iParent.getName());
				final int[] pair = { -indexParent, indexFeature };
				// Result : {-Parent, Possible FO Feature}
				possibleFOFeatures.add(pair);

				// Nativ
				indexFeature = sat4jNativeSolver.getSatInstance().getVariables().getVariable(iFeature.getName(), true);
				indexParent = sat4jNativeSolver.getSatInstance().getVariables().getVariable(iParent.getName(), false);
				// Result : {Parent, Possible FO Feature} because already signed above
				possibleFOFeaturesSeb.add(new LiteralSet(indexParent, indexFeature));
			}
		}

		checkFeatureFO(entry, sat4jSolverFull, possibleFOFeatures);
		checkFeatureFO(entry, smtInterpolSolverFull, possibleFOFeatures);
		checkFeatureFONative(entry, sat4jNativeSolver, possibleFOFeaturesSeb);

		optiFalseOptionalAnalysis.add(entry);
	}

	private void evaluateVoidAnalysis(String modelName) {
		final EvaluationEntry entry =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), sat4jSolverFull.getProblem().getClauseCount(), modelName);

		checkVoid(entry, sat4jSolverFull);
		checkVoid(entry, smtInterpolSolverFull);
		checkVoidNative(entry, sat4jNativeSolver);

		validAnalysis.add(entry);
	}

	private void evaluateCountSolutionsAnalysis(String modelName) {
		final EvaluationEntry entry =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), sat4jSolverFull.getProblem().getClauseCount(), modelName);

		// TODO SOLVERS both implementations kills the RAM :)
		// checkCountSolutions(entry, sat4jSolverFull);
		// checkCountSolutions(entry, smtInterpolSolverFull);
		checkCountSolutionsNative(entry, sat4jNativeSolver);

		countSolutions.add(entry);
	}

	/**
	 * @param entry
	 * @param sat4jNativeSolver2
	 */
	private void checkCountSolutionsNative(EvaluationEntry entry,
			de.ovgu.featureide.fm.core.analysis.cnf.solver.impl.nativesat4j.ISatSolver sat4jNativeSolver2) {

		long t1 = System.currentTimeMillis();
		final de.ovgu.featureide.fm.core.analysis.cnf.analysis.CountSolutionsAnalysis analysis =
			new de.ovgu.featureide.fm.core.analysis.cnf.analysis.CountSolutionsAnalysis(sat4jNativeSolver2);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final Long result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		entry.results.add("[" + result + "]");

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

	/**
	 * @param entry
	 * @param sat4jSolverFull2
	 */
	private void checkCountSolutions(EvaluationEntry entry, ISatSolver solver) {
		long t1 = System.currentTimeMillis();
		final CountSolutionsAnalysis analysis = new CountSolutionsAnalysis(solver);
		final long initTime = (System.currentTimeMillis() - t1);
		entry.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		final Long result = LongRunningWrapper.runMethod(analysis);
		final long ges = System.currentTimeMillis() - t1;

		entry.results.add("[" + result + "]");

		// Save time for the complete analysis
		entry.addTime(ges);
		entry.addTime(ges + initTime);
	}

}
