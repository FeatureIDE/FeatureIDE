package de.ovgu.featureide.fm.attributes.view.actions;

import java.util.Arrays;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solvers.impl.javasmt.sat.JavaSmtSatSolver;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
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

}
