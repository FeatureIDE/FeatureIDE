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
package org.prop4j.solver.impl.Ltms;

import org.prop4j.solver.AbstractSolverFactory;
import org.prop4j.solver.IMusExtractor;
import org.prop4j.solver.IOptimizationSolver;
import org.prop4j.solver.ISatProblem;
import org.prop4j.solver.ISatSolver;
import org.prop4j.solver.ISmtProblem;

/**
 * Concrete factory for Sat4J sat solver
 *
 * @author Joshua Sprey
 */
public class LtmsSatSolverFactory extends AbstractSolverFactory {

	public static final String ID = "org.prop4j.solver.impl.Ltms.LtmsSatSolverFactory";

	@Override
	public String getId() {
		return ID;
	}

	public LtmsSatSolverFactory() {}

	@Override
	public IMusExtractor getMusExtractor(ISatProblem problem) {
		return new Ltms(problem, null);
	}

	@Override
	public ISatSolver getSolver(ISatProblem problem) {
		return new Ltms(problem, null);
	}

	@Override
	public IOptimizationSolver getOptimizationSolver(ISmtProblem problem) {
		throw new UnsupportedOperationException("Ltms does not support optimizing attributes.");
	}

	@Override
	public boolean initExtension() {
		return true;
	}

	@Override
	public String getDisplayName() {
		return "LTMS";
	}

	@Override
	public String getDisplayDescription() {
		return "The logic truth maintenence system is a boolean constraint propagator. It is fast but does not always provide a solution.";
	}

	@Override
	public boolean isSupportingOptimizations() {
		return false;
	}

	@Override
	public AbstractSolverFactory getNewFactory() {
		return new LtmsSatSolverFactory();
	}

}
