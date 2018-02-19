package de.ovgu.featureide.fm.attributes.view.actions;

import java.util.Arrays;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.explain.solvers.impl.ltms.Ltms;
import org.prop4j.explain.solvers.impl.sat4j.Sat4jMusExtractor;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solver.impl.sat4j.Sat4JSatMusSolver;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolverNew;
import org.prop4j.solverOld.BasicSolver;
import org.prop4j.solverOld.SatInstance;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolver;
import org.sat4j.specs.ContradictionException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.FeatureUtils;

public class TestSolver extends Action {

	private FeatureAttributeView view;

	public TestSolver(FeatureAttributeView view, ImageDescriptor icon) {
		super("", icon);
		this.view = view;
	}

	@Override
	public void run() {
		if (view.getFeatureModel() != null) {
			// FMAttributesPlugin.getDefault().logInfo("" + view.getFeatureModel().getAnalyser().getCnf());
			Node cnf = view.getFeatureModel().getAnalyser().getCnf();
			ISatProblem problem = new SatProblem(cnf, FeatureUtils.getFeatureNamesPreorder(view.getFeatureModel()));
			testeAllMus(problem);
			// testSatSolver(problem);
		}
	}

	public void testeAllMus(ISatProblem problem) {
		JavaSmtSatSolver solver3 = new JavaSmtSatSolver(problem, Solvers.SMTINTERPOL, null);
		Literal test = new Literal("Security", true);
		solver3.push(test);

		Sat4jMusExtractor extractor = new Sat4jMusExtractor();
		Ltms ltms = new Ltms();
		for (Node clause : problem.getClauses()) {
			extractor.addClause(clause);
			ltms.addClause(clause);
		}
		extractor.addAssumption("Security", true);
		ltms.addAssumption("Security", true);

		Sat4JSatMusSolver solver4 = new Sat4JSatMusSolver(problem, null);
		solver4.push(test);
		FMCorePlugin.getDefault().logInfo("Timo:" + extractor.getAllMinimalUnsatisfiableSubsets());
		FMCorePlugin.getDefault().logInfo("Ltms:" + ltms.getAllMinimalUnsatisfiableSubsetIndexes());
		FMCorePlugin.getDefault().logInfo("JavaSmt:" + solver3.getAllMinimalUnsatisfiableSubsets());
		FMCorePlugin.getDefault().logInfo("Josh:" + solver4.getAllMinimalUnsatisfiableSubsets());
	}

	public void testeMus(ISatProblem problem) {
		JavaSmtSatSolver solver3 = new JavaSmtSatSolver(problem, Solvers.SMTINTERPOL, null);
		Literal test = new Literal("Security", true);
		solver3.push(test);

		Sat4jMusExtractor extractor = new Sat4jMusExtractor();
		for (Node clause : problem.getClauses()) {
			extractor.addClause(clause);
		}
		extractor.addAssumption("Security", true);

		Sat4JSatMusSolver solver4 = new Sat4JSatMusSolver(problem, null);
		solver4.push(test);
		FMCorePlugin.getDefault().logInfo("Timo:" + extractor.getMinimalUnsatisfiableSubset());
		FMCorePlugin.getDefault().logInfo("JavaSmt:" + solver3.getMinimalUnsatisfiableSubset());
		FMCorePlugin.getDefault().logInfo("Josh:" + solver4.getMinimalUnsatisfiableSubset());

	}

	public void testSatSolver(ISatProblem problem) {
		// Create Solvers
		try {
			BasicSolver solver0 = new BasicSolver(new SatInstance(problem.getRoot(), FeatureUtils.getFeatureNamesPreorder(view.getFeatureModel())));
			Sat4jSatSolver solver1 = new Sat4jSatSolver(problem, null);
			Sat4jSatSolverNew solver2 = new Sat4jSatSolverNew(problem, null);
			JavaSmtSatSolver solver3 = new JavaSmtSatSolver(problem, Solvers.SMTINTERPOL, null);

			int[] model0 = solver0.findModel();
			int[] model1 = SolverUtils.getIntModel(solver1.findSolution());
			int[] model2 = SolverUtils.getIntModel(solver2.findSolution());
			int[] model3 = SolverUtils.getIntModel(solver3.findSolution());

			FMCorePlugin.getDefault().logInfo("Solve:\n" + Arrays.toString(model0) + "\n" + SolverUtils.getNamesOfIndexes(problem, model0) + "\n"
				+ Arrays.toString(model1) + "\n" + SolverUtils.getNamesOfIndexes(problem, model1) + "\n" + Arrays.toString(model2) + "\n"
				+ SolverUtils.getNamesOfIndexes(problem, model2) + "\n" + Arrays.toString(model3) + "\n" + SolverUtils.getNamesOfIndexes(problem, model3));

			// Security assume to be false. Has index 16
			Literal security = new Literal("Security", false);

			// Test push literal
			solver0.assignmentPush(-16);
			solver1.push(security);
			solver2.push(security);
			solver3.push(security);

			model0 = solver0.findModel();
			model1 = SolverUtils.getIntModel(solver1.findSolution());
			model2 = SolverUtils.getIntModel(solver2.findSolution());
			model3 = SolverUtils.getIntModel(solver3.findSolution());

			FMCorePlugin.getDefault().logInfo("Pushed:\n" + Arrays.toString(model0) + "\n" + SolverUtils.getNamesOfIndexes(problem, model0) + "\n"
				+ Arrays.toString(model1) + "\n" + SolverUtils.getNamesOfIndexes(problem, model1) + "\n" + Arrays.toString(model2) + "\n"
				+ SolverUtils.getNamesOfIndexes(problem, model2) + "\n" + Arrays.toString(model3) + "\n" + SolverUtils.getNamesOfIndexes(problem, model3));

			// push the clause
			Literal newFeature2 = new Literal("NewFeature2", false);
			Literal root = new Literal("Elevator", false);
			Node newOr = new Or(newFeature2, root);

			// Test push new clause
			solver1.push(newOr);
			solver2.push(newOr);
			solver3.push(newOr);

			model1 = SolverUtils.getIntModel(solver1.findSolution());
			model2 = SolverUtils.getIntModel(solver2.findSolution());
			model3 = SolverUtils.getIntModel(solver3.findSolution());

			FMCorePlugin.getDefault()
					.logInfo("Pushed:\n" + Arrays.toString(model1) + "\n" + SolverUtils.getNamesOfIndexes(problem, model1) + "\n" + Arrays.toString(model2)
						+ "\n" + SolverUtils.getNamesOfIndexes(problem, model2) + "\n" + Arrays.toString(model3) + "\n"
						+ SolverUtils.getNamesOfIndexes(problem, model3));

		} catch (ContradictionException e) {
			FMCorePlugin.getDefault().logError(e);
		}

	}

	public void testJAvaSat(ISatProblem problem) {
		JavaSmtSatSolver solver = new JavaSmtSatSolver(problem, Solvers.SMTINTERPOL, null);

		Literal root = new Literal(view.getFeatureModel().getStructure().getRoot().getFeature().getName());
		Literal newFeature1 = new Literal("NewFeature1");
		newFeature1.positive = false;
		root.positive = false;
		Node nodeClause = new Or(newFeature1, root);

		solver.push(nodeClause);

		Object[] solution = solver.findSolution();

		if (solution != null) {
			Arrays.sort(solution);
			FMAttributesPlugin.getDefault().logInfo("O: " + "\nN:" + Arrays.toString(solution));
		} else {

			FMAttributesPlugin.getDefault().logInfo("Explanation:" + solver.getAllMinimalUnsatisfiableSubsets());
			FMAttributesPlugin.getDefault().logInfo("Explanation:" + solver.getAllMinimalUnsatisfiableSubsetIndexes());
		}
	}

}
