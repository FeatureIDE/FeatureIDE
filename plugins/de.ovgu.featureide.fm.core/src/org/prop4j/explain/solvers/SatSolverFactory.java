///* FeatureIDE - A Framework for Feature-Oriented Software Development
// * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
// *
// * This file is part of FeatureIDE.
// *
// * FeatureIDE is free software: you can redistribute it and/or modify
// * it under the terms of the GNU Lesser General Public License as published by
// * the Free Software Foundation, either version 3 of the License, or
// * (at your option) any later version.
// *
// * FeatureIDE is distributed in the hope that it will be useful,
// * but WITHOUT ANY WARRANTY; without even the implied warranty of
// * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// * GNU Lesser General Public License for more details.
// *
// * You should have received a copy of the GNU Lesser General Public License
// * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
// *
// * See http://featureide.cs.ovgu.de/ for further information.
// */
//package org.prop4j.explain.solvers;
//
//import org.prop4j.solver.IMusExtractor;
//import org.prop4j.solver.ISatProblem;
//import org.prop4j.solver.ISolver;
//import org.prop4j.solver.impl.sat4j.Sat4JSatSolverFactory;
//
///**
// * Provides instances of {@link ISatSolver}.
// *
// * @author Timo G&uuml;nther
// */
//public abstract class SatSolverFactory {
//
//	/**
//	 * Returns a default instance of this class.
//	 *
//	 * @return a default instance of this class
//	 */
//	public static SatSolverFactory getDefault() {
//		return new Sat4JSatSolverFactory();
//	}
//
//	/**
//	 * Returns an instance of {@link ISatSolver}.
//	 *
//	 * @return an instance of {@link ISatSolver}
//	 */
//	public abstract ISolver getSatSolver(ISatProblem problem);
//
//	/**
//	 * Returns an instance of {@link IMusExtractor}.
//	 *
//	 * @return an instance of {@link IMusExtractor}
//	 */
//	public abstract IMusExtractor getMusExtractor(ISatProblem problem);
//}
