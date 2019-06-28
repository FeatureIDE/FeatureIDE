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
package de.ovgu.featureide.examples.featuremodelanalysis;

import java.nio.file.Path;
import java.nio.file.Paths;

import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * An example usage of the FeatureIDE library for feature-model analysis.
 *
 * @author Thomas Thuem
 */
public class FeatureModelAnalysis {

	public static void main(String[] args) throws TimeoutException {
		final Path path = Paths.get("car.xml");
		final IFeatureModel featureModel = FeatureModelManager.load(path).getObject();
		final FeatureModelAnalyzer analyser = featureModel.getAnalyser();
		analyser.analyzeFeatureModel(null);
		System.out.println("Feature model is " + (analyser.valid() ? "not " : "") + "void");
		System.out.println("Dead features: " + analyser.getCachedDeadFeatures());
		System.out.println(analyser.getExplanation(featureModel.getFeature("Bluetooth")));
		
		SatSolver solver = new SatSolver(analyser.getCnf(), 1000);
		Node query = new Implies(new Literal("Navigation"), new Literal("Ports"));
		System.out.print("Is \"FM => (" + query + ")\" a tautology? ");
		System.out.println(!solver.isSatisfiable(new Not(query).toCNF()) ? "yes" : "no");
	}

}
