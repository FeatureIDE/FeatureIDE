package de.ovgu.featureide.fm.attributes.view.actions;

import java.util.Arrays;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;
import org.prop4j.Node;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;
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
			JavaSmtSatSolver solver = new JavaSmtSatSolver(problem, Solvers.Z3, null);
			Sat4jSatSolver solver2 = new Sat4jSatSolver(problem, null);

			Object[] solution = solver.findSolution();

			Object[] solution2 = solver2.findSolution();

			Arrays.sort(solution);
			Arrays.sort(solution2);

			FMAttributesPlugin.getDefault().logInfo("O: " + Arrays.toString(solution2) + "\nN:" + Arrays.toString(solution));
		}
	}

}
