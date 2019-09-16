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
package org.prop4j.analyses.impl.generalCopy;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.impl.JavaSmtSolverAnalysisFactory;
import org.prop4j.analyses.impl.Sat4JSolverAnalysisFactory;
import org.prop4j.analyses.impl.Sat4JSolverAnalysisFactoryTOGO;
import org.prop4j.analyses.impl.sat4j.Sat4JImplicationAnalysis;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolver;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * A collection of methods for working with {@link IFeatureModel} will replace the corresponding methods in {@link IFeatureModel}
 *
 * @author Soenke Holthusen
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke (Feature Interface)
 */
public class EvauatedFeatureModelAnaysis {

	private final IFeatureModel fm;
	private AdvancedNodeCreator nodeCreator;

	protected SatProblem allModelProblem;
	protected SatProblem structureModelProblem;
	protected SatProblem constraintModelProblem;

	public static List<EvaluationEntry> validAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> cleanCoreDeadAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> optiCoreDeadAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> sat4CoreDeadAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> cleanFalseOptionalAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> optiFalseOptionalAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> sat4FalseOptionalAnalysis = new ArrayList<>();
	public static List<EvaluationEntry> tautologicalConstraints = new ArrayList<>();
	public static List<EvaluationEntry> redundantConstraints = new ArrayList<>();

	HashMap<AbstractSolverAnalysisFactory, HashMap<String, Object>> predefinedList;
	AbstractSolverAnalysisFactory factory;
	AbstractSolverAnalysisFactory factorySat4j;
	AbstractSolverAnalysisFactory factoryZ3;
	AbstractSolverAnalysisFactory factoryPrincess;
	AbstractSolverAnalysisFactory factorySMTInterpol;

	LinkedList<AbstractSolverAnalysisFactory> factoryList;

	public EvauatedFeatureModelAnaysis(IFeatureModel fm, AbstractSolverAnalysisFactory factory) {
		this.fm = fm;

		final HashMap<String, Object> javaSMTZ3 = new HashMap<>();
		javaSMTZ3.put(JavaSmtSatSolver.SOLVER_TYPE, Solvers.Z3);
		final HashMap<String, Object> javaSMTPrincess = new HashMap<>();
		javaSMTPrincess.put(JavaSmtSatSolver.SOLVER_TYPE, Solvers.PRINCESS);
		final HashMap<String, Object> javaSMTSMTInterpol = new HashMap<>();
		javaSMTSMTInterpol.put(JavaSmtSatSolver.SOLVER_TYPE, Solvers.SMTINTERPOL);

		factorySat4j = AbstractSolverAnalysisFactory.getDefault();
		factoryZ3 = AbstractSolverAnalysisFactory.getJavaSmtFactory();
		factoryZ3.setDefaultConfiguration(javaSMTZ3);
		factorySMTInterpol = AbstractSolverAnalysisFactory.getJavaSmtFactory();
		factorySMTInterpol.setDefaultConfiguration(javaSMTSMTInterpol);
		factoryPrincess = AbstractSolverAnalysisFactory.getJavaSmtFactory();
		factoryPrincess.setDefaultConfiguration(javaSMTPrincess);

		factoryList = new LinkedList<>();
		factoryList.add(factorySat4j);
		factoryList.add(factorySMTInterpol);
		factoryList.add(factoryPrincess);
		factoryList.add(factoryZ3);

		doMagic();
	}

	public static void printResult() {
		printResultHidden("Valid", validAnalysis);
		printResultHidden("CleanCoreDead", cleanCoreDeadAnalysis);
		printResultHidden("OptiCoreDead", optiCoreDeadAnalysis);
		printResultHidden("Sat4jCoreDead", sat4CoreDeadAnalysis);
		printResultHidden("CleanFalseOptional", cleanFalseOptionalAnalysis);
		printResultHidden("OptiFalseOptional", optiFalseOptionalAnalysis);
		printResultHidden("Sat4jFalseOptional", sat4FalseOptionalAnalysis);
		printResultHidden("TautologicalConstraints", tautologicalConstraints);
		printResultHidden("RedundantConstraints", redundantConstraints);
	}

	private static void printResultHidden(String filename, List<EvaluationEntry> entryList) {
		final String filetowrite =
			"C:\\Users\\Joshua\\Documents\\bachelorarbeit-joshua-sprey-chico-sundermann\\data\\Evaluation_Sprey\\Data\\" + filename + ".txt";
		try (FileWriter fw = new FileWriter(filetowrite)) {
			fw.write(
					"Model | AnzahlFeatures | AnzahlConstraints | AnzahlKlauseln | Sat4J - init | Sat4J - push+pop | Sat4J - isSatisfiable | Sat4J - Gesamt ASolver | Sat4J - GesamtAnalyse | SMTInterpol - init | SMTInterpol - push+pop | SMTInterpol - isSatisfiable | SMTInterpol - Gesamt ASolver | SMTInterpol - GesamtAnalyse | Princess - init | Princess - push+pop | Princess - isSatisfiable | Princess - Gesamt ASolver | Princess - GesamtAnalyse | Z3 - init | Z3 - push+pop | Z3 - isSatisfiable | Z3 - Gesamt ASolver | Z3 - GesamtAnalyse\n");
			for (final EvaluationEntry evaluationEntry : entryList) {
				fw.write(evaluationEntry.toString() + "\n");
			}
		} catch (final IOException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private void doMagic() {

		nodeCreator = new AdvancedNodeCreator(fm);
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		nodeCreator.setUseOldNames(false);

		// Only create the cnf one time for every mode
		nodeCreator.setModelType(ModelType.All);
		allModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		nodeCreator.setModelType(ModelType.OnlyStructure);
		structureModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));
		nodeCreator.setModelType(ModelType.OnlyConstraints);
		constraintModelProblem = new SatProblem(nodeCreator.createNodes(), FeatureUtils.getFeatureNamesPreorder(fm));

		final String name = fm.getSourceFile().getName(fm.getSourceFile().getNameCount() - 1).toString();

		// ValidAnalysis
		// evaluateValid(name);

		// Core and Dead feature analyses
		// evaluateClearCoreDead(name);
		// evaluateOptiCoreDead(name);
		// evaluateSat4jCoreDead(name);

		// False optional feature analyses
		final List<int[]> possibleFOFeatures = new ArrayList<>();
		for (final IFeature feature : fm.getFeatures()) {
			final IFeature parent = FeatureUtils.getParent(feature);
			if ((parent != null) && (!feature.getStructure().isMandatorySet() || !parent.getStructure().isAnd())) {
				possibleFOFeatures
						.add(new int[] { -allModelProblem.getIndexOfVariable(parent.getName()), allModelProblem.getIndexOfVariable(feature.getName()) });
			}
		}

		// evaluateClearFalseOptional(name, possibleFOFeatures);
		// evaluateOptiFalseOptional(name, possibleFOFeatures);
		// evaluateSat4jFalseOptional(name, possibleFOFeatures);

		// evaluateRedundantConstraints(name);
		// evaluateTautologicalConstraints(name);
	}

	private void evaluateTautologicalConstraints(String modelName) {
		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;
			checkConstraintTautology(entry);
		}
		tautologicalConstraints.add(entry);
	}

	private void evaluateRedundantConstraints(String modelName) {
		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;
			checkConstraintRedundant(fm.getConstraints(), entry);
		}
		redundantConstraints.add(entry);
	}

	private void evaluateSat4jFalseOptional(String modelName, List<int[]> possibleFOFeatures) {
		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;

			if ((factory instanceof Sat4JSolverAnalysisFactory) || (factory instanceof Sat4JSolverAnalysisFactoryTOGO)) {
				checkSat4JFeatureFalseOptional(possibleFOFeatures, entry);
			}

		}
		sat4FalseOptionalAnalysis.add(entry);
	}

	private void evaluateOptiFalseOptional(String modelName, List<int[]> possibleFOFeatures) {
		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;

			// Valid Analysis
			checkFeatureFalseOptional(possibleFOFeatures, entry);

		}
		optiFalseOptionalAnalysis.add(entry);
	}

	private void evaluateClearFalseOptional(String modelName, List<int[]> possibleFOFeatures) {
		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;

			if (factory instanceof JavaSmtSolverAnalysisFactory) {
				final JavaSmtSolverAnalysisFactory jSMTFactory = (JavaSmtSolverAnalysisFactory) factory;
				final Object solverType = jSMTFactory.getDefaultConfiguration().get(JavaSmtSatSolver.SOLVER_TYPE);
				if ((solverType != null) && (solverType instanceof Solvers)) {
					// Valid Analysis
					if (((Solvers) solverType) == Solvers.Z3) {
						checkCleanFeatureFalseOptional(possibleFOFeatures, entry);
					}
				}
			}
		}
		cleanFalseOptionalAnalysis.add(entry);
	}

//	private void evaluateSat4jCoreDead(String modelName) {
//		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
//		for (final AbstractSolverAnalysisFactory factory : factoryList) {
//			this.factory = factory;
//
//			if ((factory instanceof Sat4JSolverAnalysisFactory) || (factory instanceof Sat4JSolverAnalysisFactoryTOGO)) {
//				checkSat4jFeatureDead(entry);
//			}
//
//		}
//		sat4CoreDeadAnalysis.add(entry);
//	}

	private void evaluateOptiCoreDead(String modelName) {
		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;

			// Valid Analysis
			checkFeatureDead(entry);
		}
		optiCoreDeadAnalysis.add(entry);
	}

	private void evaluateClearCoreDead(String modelName) {
		final EvaluationEntry entry = new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;

			// Valid Analysis
			checkCleanFeatureDead(entry);

		}
		cleanCoreDeadAnalysis.add(entry);
	}

	private void evaluateValid(String modelName) {
		final EvaluationEntry entryValid =
			new EvaluationEntry(fm.getNumberOfFeatures(), fm.getConstraintCount(), allModelProblem.getClauses().length, modelName);
		for (final AbstractSolverAnalysisFactory factory : factoryList) {
			this.factory = factory;

			// Valid Analysis
			checkValidity(allModelProblem, entryValid);

		}
		validAnalysis.add(entryValid);
	}

	private void checkValidity(final SatProblem modelProblem, EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final ValidAnalysis validAnalysis = (ValidAnalysis) factory.getAnalysis(ValidAnalysis.class, modelProblem);
		final long initTime = (System.currentTimeMillis() - t1);
		entryValid.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(validAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		// Save time for the push pop operations
		entryValid.addTime(validAnalysis.editTime);
		// Save time for solving
		entryValid.addTime(validAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(validAnalysis.gesamtTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime);
	}

	private void checkFeatureDead(EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final CoreDeadAnalysis coreDeadAnalysis = (CoreDeadAnalysis) factory.getAnalysis(CoreDeadAnalysis.class, allModelProblem);
		final long initTime = (System.currentTimeMillis() - t1);
		entryValid.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(coreDeadAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		// Save time for the push pop operations
		entryValid.addTime(coreDeadAnalysis.editTime);
		// Save time for solving
		entryValid.addTime(coreDeadAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(coreDeadAnalysis.gesamtTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime);
	}

	private void checkCleanFeatureDead(EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final ClearCoreDeadAnalysis coreDeadAnalysis = (ClearCoreDeadAnalysis) factory.getAnalysis(ClearCoreDeadAnalysis.class, allModelProblem);
		final long initTime = (System.currentTimeMillis() - t1);
		entryValid.addTime(initTime);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(coreDeadAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		// Save time for the push pop operations
		entryValid.addTime(coreDeadAnalysis.editTime);
		// Save time for solving
		entryValid.addTime(coreDeadAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(coreDeadAnalysis.gesamtTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime);
	}

//	private void checkSat4jFeatureDead(EvaluationEntry entryValid) {
//		// Save time to create analysis which involves the creation of the solver
//		long t1 = System.currentTimeMillis();
//		final Sat4JCoreDeadAnalysis coreDeadAnalysis = (Sat4JCoreDeadAnalysis) factory.getAnalysis(Sat4JCoreDeadAnalysis.class, allModelProblem);
//		final long initTime = (System.currentTimeMillis() - t1);
//		entryValid.addTime(initTime);
//
//		// Save time run the complete analysis
//		t1 = System.currentTimeMillis();
//		LongRunningWrapper.runMethod(coreDeadAnalysis);
//		final long ges = System.currentTimeMillis() - t1;
//
//		// Save time for the push pop operations
//		entryValid.addTime(coreDeadAnalysis.editTime);
//		// Save time for solving
//		entryValid.addTime(coreDeadAnalysis.solveTime);
//		// Save time for every data structure operation
//		entryValid.addTime(coreDeadAnalysis.gesamtTime);
//		// Save time for the complete analysis
//		entryValid.addTime(ges + initTime);
//	}

	private void checkFeatureFalseOptional(List<int[]> possibleFOFeatures, EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final ImplicationAnalysis implicationAnalysis = (ImplicationAnalysis) factory.getAnalysis(ImplicationAnalysis.class, allModelProblem);
		final long initTime = (System.currentTimeMillis() - t1);
		entryValid.addTime(initTime);

		implicationAnalysis.initParis(possibleFOFeatures);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(implicationAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		// Save time for the push pop operations
		entryValid.addTime(implicationAnalysis.editTime);
		// Save time for solving
		entryValid.addTime(implicationAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(implicationAnalysis.gesamtTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime);
	}

	private void checkCleanFeatureFalseOptional(List<int[]> possibleFOFeatures, EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final ClearImplicationAnalysis implicationAnalysis = (ClearImplicationAnalysis) factory.getAnalysis(ClearImplicationAnalysis.class, allModelProblem);
		final long initTime = (System.currentTimeMillis() - t1);
		entryValid.addTime(initTime);

		implicationAnalysis.initParis(possibleFOFeatures);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(implicationAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		// Save time for the push pop operations
		entryValid.addTime(implicationAnalysis.editTime);
		// Save time for solving
		entryValid.addTime(implicationAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(implicationAnalysis.gesamtTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime);
	}

	private void checkSat4JFeatureFalseOptional(List<int[]> possibleFOFeatures, EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final Sat4JImplicationAnalysis implicationAnalysis = (Sat4JImplicationAnalysis) factory.getAnalysis(Sat4JImplicationAnalysis.class, allModelProblem);
		final long initTime = (System.currentTimeMillis() - t1);
		entryValid.addTime(initTime);

		implicationAnalysis.setPairs(possibleFOFeatures);

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(implicationAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		// Save time for the push pop operations
		entryValid.addTime(implicationAnalysis.editTime);
		// Save time for solving
		entryValid.addTime(implicationAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(implicationAnalysis.gesamtTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime);
	}

	private void checkConstraintRedundant(final List<IConstraint> constraints, EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final RedundantConstraintAnalysis redundantAnalysis =
			(RedundantConstraintAnalysis) factory.getAnalysis(RedundantConstraintAnalysis.class, allModelProblem);
		final long initTime = (System.currentTimeMillis() - t1);
		entryValid.addTime(initTime);

		redundantAnalysis.setConstraints(fm.getConstraints());

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(redundantAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		// Save time for the push pop operations
		entryValid.addTime(redundantAnalysis.editTime);
		// Save time for solving
		entryValid.addTime(redundantAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(redundantAnalysis.gesamtTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime);
	}

	private void checkConstraintTautology(EvaluationEntry entryValid) {
		// Save time to create analysis which involves the creation of the solver
		long t1 = System.currentTimeMillis();
		final TautologicalConstraintAnalysis tautologyAnalysis =
			(TautologicalConstraintAnalysis) factory.getAnalysis(TautologicalConstraintAnalysis.class, allModelProblem);
		final long initTime = (System.currentTimeMillis() - t1);

		tautologyAnalysis.init(fm.getConstraints());

		// Save time run the complete analysis
		t1 = System.currentTimeMillis();
		LongRunningWrapper.runMethod(tautologyAnalysis);
		final long ges = System.currentTimeMillis() - t1;

		entryValid.addTime(initTime + tautologyAnalysis.editTime);
		entryValid.addTime(0);
		// Save time for solving
		entryValid.addTime(tautologyAnalysis.solveTime);
		// Save time for every data structure operation
		entryValid.addTime(tautologyAnalysis.gesamtTime - tautologyAnalysis.editTime);
		// Save time for the complete analysis
		entryValid.addTime(ges + initTime + tautologyAnalysis.editTime);
	}
}
