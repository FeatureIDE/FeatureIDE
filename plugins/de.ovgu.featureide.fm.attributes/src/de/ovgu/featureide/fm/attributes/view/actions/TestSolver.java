package de.ovgu.featureide.fm.attributes.view.actions;

import java.util.Arrays;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.prop4j.Constant;
import org.prop4j.DoubleType;
import org.prop4j.Function;
import org.prop4j.GreaterThan;
import org.prop4j.IntegerType;
import org.prop4j.LessThan;
import org.prop4j.Node;
import org.prop4j.Variable;
import org.prop4j.analyses.AbstractSolverAnalysisFactory;
import org.prop4j.analyses.impl.general.CoreDeadAnalysis;
import org.prop4j.solver.ISolverProblem;
import org.prop4j.solver.impl.SatProblem;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

public class TestSolver extends Action {

	private FeatureAttributeView view;

	public TestSolver(FeatureAttributeView view, ImageDescriptor icon) {
		super("", icon);
		this.view = view;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	@Override
	public void run() {
		if (view.getFeatureModel() != null) {
			// FMAttributesPlugin.getDefault().logInfo("" + view.getFeatureModel().getAnalyser().getCnf());
			Node cnf = view.getFeatureModel().getAnalyser().getCnf();
			solveSatRequestWithSMT(cnf);
		}
	}

	private void solveSatRequestWithSMT(Node cnf) {
		ISolverProblem problem = new SatProblem(cnf, FeatureUtils.getFeatureNamesPreorder(view.getFeatureModel()));

		// FMAttributesPlugin.getDefault().logInfo(cnf.toString());

		Constant<IntegerType> constant40 = new Constant<IntegerType>(40);
		Constant<DoubleType> constant80 = new Constant<DoubleType>(80.0D);
		Variable<DoubleType> variableDouble = new Variable<DoubleType>("Featurepreis");
		Function addition4080 = Function.substract(constant40, constant80);
		Function addition40802 = Function.divide(constant40, constant80);
		Function addition40803 = Function.multiply(constant40, constant80);
		Function addition40804 = Function.modulo(constant40, constant80);
		Function addition40805 = Function.newgate(constant40);

		GreaterThan gT = new GreaterThan(constant80, constant40);
		LessThan lT = new LessThan(addition4080, variableDouble);
		LessThan lT2 = new LessThan(addition40802, variableDouble);
		LessThan lT3 = new LessThan(addition40803, variableDouble);
		LessThan lT4 = new LessThan(addition40804, variableDouble);
		LessThan lT5 = new LessThan(addition40805, variableDouble);

		Node[] children = cnf.getChildren();
		Node[] newChildren = new Node[children.length + 6];

		for (int i = 0; i < newChildren.length - 6; i++) {
			newChildren[i] = children[i];
		}
		newChildren[newChildren.length - 6] = gT;
		newChildren[newChildren.length - 5] = lT;
		newChildren[newChildren.length - 4] = lT2;
		newChildren[newChildren.length - 3] = lT3;
		newChildren[newChildren.length - 2] = lT4;
		newChildren[newChildren.length - 1] = lT5;

		Node cnfCopy = cnf.clone();
		cnfCopy.setChildren(newChildren);

		AbstractSolverAnalysisFactory factory = AbstractSolverAnalysisFactory.getDefault();

		CoreDeadAnalysis test = (CoreDeadAnalysis) factory.getAnalysis(CoreDeadAnalysis.class, problem);
		try {
			int[] solution = LongRunningWrapper.runMethod(test, new NullMonitor());
			String solutionString = "[";
			for (int i : solution) {
				solutionString += ", " + problem.getVariableOfIndex(Math.abs(i));
			}
			solutionString += "]";
			FMAttributesPlugin.getDefault().logInfo("MySolution: " + solutionString + "\t" + Arrays.toString(solution));
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

//		FMAttributesPlugin.getDefault().logInfo("Is Satis: " + new Sat4jSatSolverFactory().getSatSolver().isSatisfiable(cnf));
//		Configuration config;
//		try {
//			config = Configuration.defaultConfiguration();
//			LogManager logger = BasicLogManager.create(config);
//			ShutdownManager shutdown = ShutdownManager.create();
//
//			SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(), Solvers.SMTINTERPOL);
//
//			FormulaManager fmgr = context.getFormulaManager();
//
//			BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
//			IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
//
//			ArrayList<BooleanFormula> clauses = new ArrayList<>();
//			for (Node clause : cnf.getChildren()) {
//
//				ArrayList<BooleanFormula> literals = new ArrayList<>();
//				// Get the contained features and add them as literals
//				for (int i = 0; i < clause.getChildren().length; i++) {
//					String literal = clause.getChildren()[i].toString();
//					if (literal.contains("-")) {
//						literal = literal.replaceAll("-", "");
//						literals.add(bmgr.not(bmgr.makeVariable(literal)));
//					} else {
//						literals.add(bmgr.makeVariable(literal));
//					}
//				}
//				BooleanFormula clauseFormula = bmgr.or(literals);
//				clauses.add(clauseFormula);
//			}
//
//			BooleanFormula cnfFormula = bmgr.and(clauses);
//			try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
//				prover.addConstraint(cnfFormula);
//
//				boolean isSat = !prover.isUnsat();
//			} catch (SolverException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			} catch (InterruptedException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
//		} catch (InvalidConfigurationException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
////		}
	}

}
