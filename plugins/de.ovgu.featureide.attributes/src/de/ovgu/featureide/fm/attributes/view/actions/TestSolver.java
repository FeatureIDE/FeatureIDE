package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.prop4j.Node;
import org.prop4j.explain.solvers.impl.sat4j.Sat4jSatSolverFactory;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;

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
		FMAttributesPlugin.getDefault().logInfo("Is Satis: " + new Sat4jSatSolverFactory().getSatSolver().isSatisfiable(cnf));
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
