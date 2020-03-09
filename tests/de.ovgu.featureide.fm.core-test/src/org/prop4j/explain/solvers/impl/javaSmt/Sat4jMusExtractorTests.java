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
package org.prop4j.explain.solvers.impl.javaSmt;

import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractorTests;
import org.prop4j.solver.IMusExtractor;
import org.prop4j.solver.impl.SatProblem;
import org.prop4j.solver.impl.sat4j.Sat4JSatSolverFactory;

/**
 * Tests for {@link Sat4jMusExtractor}.
 *
 * @author Timo G&uuml;nther
 */
public class Sat4jMusExtractorTests extends MusExtractorTests {

	@Override
	protected IMusExtractor getInstance(Node cnf) {
		if (cnf != null) {
			cnf = cnf.toRegularCNF();
		}
		return new Sat4JSatSolverFactory().getExplanationSolver(new SatProblem(cnf));
	}

}
