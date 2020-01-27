/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.examples.featuremodelanalysis;

import java.nio.file.Path;
import java.nio.file.Paths;

import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.Nodes;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.SimpleSatSolver;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * An example usage of the FeatureIDE library for feature-model analysis.
 *
 * @author Thomas Thuem
 */
public class FeatureModelAnalysis {

	public static void main(String[] args) throws TimeoutException {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
		final Path path = Paths.get("car.xml");
		final IFeatureModel featureModel = FeatureModelManager.load(path);
		if (featureModel != null) {
			FeatureModelFormula formula = new FeatureModelFormula(featureModel);
			final FeatureModelAnalyzer analyzer = formula.getAnalyzer();
			analyzer.analyzeFeatureModel(null);
			System.out.println("Feature model is " + (analyzer.isValid(null) ? "not " : "") + "void");
			System.out.println("Dead features: " + analyzer.getDeadFeatures(null));
			System.out.println(analyzer.getExplanation(featureModel.getFeature("Bluetooth")));

			final SimpleSatSolver solver = new SimpleSatSolver(formula.getCNF());
			final Node query = new Implies(new Literal("Navigation"), new Literal("Ports"));
			System.out.print("Is \"FM => (" + query + ")\" a tautology? ");
			ClauseList queryClauses = Nodes.convert(formula.getCNF().getVariables(), new Not(query), true);
			solver.addClauses(queryClauses);
			switch (solver.hasSolution()) {
			case FALSE:
				System.out.println("yes");
				break;
			case TRUE:
				System.out.println("no");
				break;
			case TIMEOUT:
				System.out.println("cannot decide (timeout)");
				break;
			default:
				break;
			}
		} else {
			System.out.println("Feature model could not be read!");
		}
	}

}
