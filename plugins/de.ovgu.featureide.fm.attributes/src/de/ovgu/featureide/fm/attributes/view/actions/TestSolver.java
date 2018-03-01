package de.ovgu.featureide.fm.attributes.view.actions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.prop4j.And;
import org.prop4j.Constant;
import org.prop4j.Equal;
import org.prop4j.Function;
import org.prop4j.GreaterThan;
import org.prop4j.Implies;
import org.prop4j.IntegerType;
import org.prop4j.LessThan;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.Variable;
import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.impl.smt.FeatureAttributeRangeAnalysis;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solver.impl.SmtProblem;
import org.prop4j.solver.impl.SolverUtils;
import org.prop4j.solver.impl.sat4j.Sat4JSatMusSolver;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;
import org.prop4j.solverOld.BasicSolver;
import org.prop4j.solverOld.SatInstance;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatMusExtractor;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolver;
import org.prop4j.solvers.impl.javasmt.smt.JavaSmtSolver;
import org.sat4j.specs.ContradictionException;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

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

			testeAttributeRanges(cnf);
			// testeMus(problem);
			// testSatSolver(problem);
		}
	}

	private void testeAttributeRanges(Node cnf) {
//		Dein Problem erstellen
		Variable<IntegerType> sum = new Variable<IntegerType>("sum", new IntegerType(12));
		Variable<IntegerType> feat1a = new Variable<IntegerType>("feat1a", new IntegerType(23));
		Variable<IntegerType> feat2a = new Variable<IntegerType>("feat2a", new IntegerType(23));
		Variable<IntegerType> feat3a = new Variable<IntegerType>("feat3a", new IntegerType(23));

		List<String> variables = new ArrayList<>();
		variables.addAll(FeatureUtils.getFeatureNamesPreorder(view.getFeatureModel()));
		variables.add("feat1a");
		variables.add("feat2a");
		variables.add("feat3a");
		variables.add("sum");

		Node impl1 = new Implies(variables.get(0), new Equal(feat1a, new Constant<IntegerType>(new IntegerType(23))));
		Node impl2 = new Implies(new Not(variables.get(0)), new Equal(feat1a, new Constant<IntegerType>(new IntegerType(0))));

		Node impl11 = new Implies(variables.get(1), new Equal(feat2a, new Constant<IntegerType>(new IntegerType(23))));
		Node impl12 = new Implies(new Not(variables.get(1)), new Equal(feat2a, new Constant<IntegerType>(new IntegerType(0))));

		Node impl21 = new Implies(variables.get(2), new Equal(feat3a, new Constant<IntegerType>(new IntegerType(23))));
		Node impl22 = new Implies(new Not(variables.get(2)), new Equal(feat3a, new Constant<IntegerType>(new IntegerType(0))));

		Node attributeSum = new Equal(sum, Function.sum(feat1a, feat2a, feat3a));

		Constant<IntegerType> nst500 = new Constant<IntegerType>(new IntegerType(500));
		Constant<IntegerType> nst300 = new Constant<IntegerType>(new IntegerType(300));

		Node test = new GreaterThan(nst500, sum);
		Node test2 = new LessThan(nst300, sum);

//		Node eq = new GreaterEqual(new Variable<IntegerType>("LOL", new IntegerType(0)), new Constant<IntegerType>(new IntegerType(24)));
//		Node less = new LessThan(new Variable<IntegerType>("TestVar", new IntegerType(0)), new Constant<IntegerType>(new IntegerType(5580)));
//		Node eq2 = new Equal(new Variable<IntegerType>("TestVar", new IntegerType(0)),
//				Function.sum(new Constant<IntegerType>(new IntegerType(5555)), new Variable<IntegerType>("LOL", new IntegerType(0))));
//
//		variables.add("TestVar");
//		variables.add("LOL");

//		Node and = new And(cnf, eq, less, eq2);

//		Node and = new And(test, test2);
		Node and = new And(cnf, impl1, impl2, impl11, impl12, impl21, impl22, attributeSum);
		FMCorePlugin.getDefault().logInfo(and.toString());

		SmtProblem dummy = new SmtProblem(and, variables);

		AbstractSolverAnalysisFactory factory = AbstractSolverAnalysisFactory.getJavaSmtFactory();

		FeatureAttributeRangeAnalysis analysis = (FeatureAttributeRangeAnalysis) factory.getAnalysis(FeatureAttributeRangeAnalysis.class, dummy);
		analysis.setVariable("sum");
		analysis.getSolver().setConfiguration(JavaSmtSolver.SOLVER_TYPE, Solvers.Z3);
		Object result = LongRunningWrapper.runMethod(analysis, new NullMonitor());
		FMCorePlugin.getDefault().logInfo("" + result);
		// falls nötig
		// analysis.getSolver().push(formula);

	}

	public void testeAllMus(ISatProblem problem) {
		try {
			JavaSmtSatMusExtractor solver3 = new JavaSmtSatMusExtractor(problem, Solvers.SMTINTERPOL, null);
			Node test = new And(new Or(new Literal("Security"), new Literal("Security2")), new Implies(new Literal("Base"), new Literal("Security", false)));
			test = test.toRegularCNF();
			solver3.push(new Literal("Security", true));
			solver3.push(test.getChildren());

//			Sat4jMusExtractor extractor = new Sat4jMusExtractor();
//			Ltms ltms = new Ltms();
//			for (Node clause : problem.getClauses()) {
//				extractor.addClause(clause);
//				ltms.addClause(clause);
//			}
//			extractor.addAssumption("Security", true);
//			ltms.addClause(test.getChildren()[0]);
//			ltms.addClause(test.getChildren()[1]);
//			ltms.addAssumption("Security", true);

			Sat4JSatMusSolver solver4 = new Sat4JSatMusSolver(problem, null);

			solver4.push(new Literal("Security", true));
			solver4.push(test.getChildren());

//			FMCorePlugin.getDefault().logInfo("Timo:" + extractor.getAllMinimalUnsatisfiableSubsets());
//			FMCorePlugin.getDefault().logInfo("Ltms:" + ltms.getAllMinimalUnsatisfiableSubsetIndexes());
			FMCorePlugin.getDefault().logInfo("JavaSmt:" + solver3.getAllMinimalUnsatisfiableSubsets());
			FMCorePlugin.getDefault().logInfo("Josh:" + solver4.getAllMinimalUnsatisfiableSubsets());
		} catch (org.prop4j.solver.ContradictionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public void testeMus(ISatProblem problem) {
		try {
			JavaSmtSatMusExtractor solver3 = new JavaSmtSatMusExtractor(problem, Solvers.SMTINTERPOL, null);
			Literal test = new Literal("Security", true);
			solver3.push(test);

//			Sat4jMusExtractor extractor = new Sat4jMusExtractor();
//			for (Node clause : problem.getClauses()) {
//				extractor.addClause(clause);
//			}
//			extractor.addAssumption("Security", true);

			Sat4JSatMusSolver solver4 = new Sat4JSatMusSolver(problem, null);
			solver4.push(test);
//			FMCorePlugin.getDefault().logInfo("Timo:" + extractor.getMinimalUnsatisfiableSubset());
			FMCorePlugin.getDefault().logInfo("JavaSmt:" + solver3.getMinimalUnsatisfiableSubset());
			FMCorePlugin.getDefault().logInfo("Josh:" + solver4.getMinimalUnsatisfiableSubset());
		} catch (org.prop4j.solver.ContradictionException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	public void testSatSolver(ISatProblem problem) {
		// Create Solvers
		try {
			BasicSolver solver0 = new BasicSolver(new SatInstance(problem.getRoot(), FeatureUtils.getFeatureNamesPreorder(view.getFeatureModel())));
			Sat4jSatSolver solver1 = new Sat4jSatSolver(problem, null);
			Sat4jSatSolver solver2 = new Sat4jSatSolver(problem, null);
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

		} catch (org.prop4j.solver.ContradictionException e) {
			FMCorePlugin.getDefault().logError(e);
		} catch (ContradictionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	public void testJAvaSat(ISatProblem problem) {
		JavaSmtSatMusExtractor solver = new JavaSmtSatMusExtractor(problem, Solvers.SMTINTERPOL, null);

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
