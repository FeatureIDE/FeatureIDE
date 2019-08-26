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
//package org.prop4j.analyses.impl.sat4j;
//
//import org.prop4j.solver.AbstractSatSolver;
//import org.prop4j.solver.ContradictionException;
//import org.prop4j.solver.ISatSolver.SelectionStrategy;
//import org.prop4j.solver.impl.SolverUtils;
//import org.prop4j.solver.impl.sat4j.Sat4jSatSolver;
//import org.sat4j.core.VecInt;
//
//import de.ovgu.featureide.fm.core.FMCorePlugin;
//import de.ovgu.featureide.fm.core.conf.AFeatureGraph;
//import de.ovgu.featureide.fm.core.conf.IFeatureGraph;
//import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
//
///**
// * Finds core and dead features.
// *
// * @author Sebastian Krieter
// */
//public class Sat4JConditionallyCoreDeadAnalysisFG extends Sat4JAConditionallyCoreDeadAnalysis {
//
//	private final IFeatureGraph featureGraph;
//
//	public Sat4JConditionallyCoreDeadAnalysisFG(Sat4jSatSolver solver, IFeatureGraph featureGraph) {
//		super(solver);
//		this.featureGraph = featureGraph;
//	}
//
//	@Override
//	public int[] analyze(IMonitor monitor) {
//		satCount = 0;
////		solver.getAssignment().ensure(fixedVariables.length);
//		for (int i = 0; i < fixedVariables.length; i++) {
//			final int var = fixedVariables[i];
//			try {
//				solver.push(getLiteralFromIndex(var));
//			} catch (final ContradictionException e) {
//				FMCorePlugin.getDefault().logError(e);
//			}
//		}
//		solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.POSITIVE);
//		final int[] model1 = SolverUtils.getIntModel(solver.findSolution());
//		satCount++;
//
//		if (model1 != null) {
//			solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.NEGATIVE);
//			final int[] model2 = SolverUtils.getIntModel(solver.findSolution());
//			satCount++;
//
//			// if there are more negative than positive literals
//			if ((model1.length < (countNegative(model2) + countNegative(model1)))) {
//				solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.POSITIVE);
//			} else {
//				solver.setConfiguration(AbstractSatSolver.CONFIG_SELECTION_STRATEGY, SelectionStrategy.NEGATIVE);
//
//			}
//
//			SolverUtils.updateModel(model1, model2);
//			for (int i = 0; i < fixedVariables.length; i++) {
//				model1[Math.abs(fixedVariables[i]) - 1] = 0;
//			}
//
//			final VecInt v = new VecInt();
//			for (int i = 0; i < newCount; i++) {
//				final int var = fixedVariables[i];
//				traverse(model1, v, var);
//			}
//
//			sat(model1, v);
//		}
//		return getIntegerAssumptions();
//	}
//
//	private void sat(int[] model1, VecInt v) {
//		try {
//			while (!v.isEmpty()) {
//				final int varX = v.get(v.size() - 1);
//				v.pop();
//				if (model1[Math.abs(varX) - 1] == varX) {
//					solver.push(getLiteralFromIndex(-varX));
//					satCount++;
//					switch (solver.isSatisfiable()) {
//					case FALSE:
//						solver.pop();
//						solver.push(getLiteralFromIndex(-varX));
//						traverse2(v, varX);
//						break;
//					case TIMEOUT:
//						throw new RuntimeException();
//					case TRUE:
//						solver.pop();
//						SolverUtils.updateModel(model1, SolverUtils.getIntModel(solver.findSolution()));
////					solver.shuffleOrder();
//						break;
//					}
//				}
//			}
//		} catch (final ContradictionException e) {
//			FMCorePlugin.getDefault().logError(e);
//		}
//	}
//
//	private void traverse(int[] model1, VecInt v, int var) {
//		final boolean fromSelected = var > 0;
//
//		for (int j = 0; j < model1.length; j++) {
//			if (model1[j] != 0) {
//				final byte value = featureGraph.getValueInternal(Math.abs(var) - 1, j, fromSelected);
//				switch (value) {
//				case AFeatureGraph.VALUE_0:
//					try {
//						solver.push(getLiteralFromIndex((-(j + 1))));
//					} catch (final ContradictionException e) {
//						FMCorePlugin.getDefault().logError(e);
//					}
//					break;
//				case AFeatureGraph.VALUE_1:
//					try {
//						solver.push(getLiteralFromIndex(((j + 1))));
//					} catch (final ContradictionException e) {
//						FMCorePlugin.getDefault().logError(e);
//					}
//					break;
//				case AFeatureGraph.VALUE_0Q:
//					v.push(-(j + 1));
//					break;
//				case AFeatureGraph.VALUE_1Q:
//					v.push(j + 1);
//					break;
//				case AFeatureGraph.VALUE_10Q:
//					v.push(j + 1);
//					v.push(-(j + 1));
//					break;
//				default:
//					break;
//				}
//			}
//		}
//	}
//
//	private void traverse2(VecInt v, int var) {
//		final boolean fromSelected = var > 0;
//
//		for (int i = v.size() - 1; i >= 0; i--) {
//			final int varX = v.get(i);
//			final byte value = featureGraph.getValueInternal(Math.abs(var) - 1, Math.abs(varX) - 1, fromSelected);
//			switch (value) {
//			case AFeatureGraph.VALUE_0:
//				if (varX < 0) {
//					try {
//						solver.push(getLiteralFromIndex(varX));
//					} catch (final ContradictionException e) {
//						FMCorePlugin.getDefault().logError(e);
//					}
//				}
//				v.delete(i);
//				break;
//			case AFeatureGraph.VALUE_1:
//				if (varX > 0) {
//					try {
//						solver.push(getLiteralFromIndex(varX));
//					} catch (final ContradictionException e) {
//						FMCorePlugin.getDefault().logError(e);
//					}
//				}
//				v.delete(i);
//				break;
//			default:
//				break;
//			}
//		}
//	}
//
//	@Override
//	public String toString() {
//		return "FG_Improved";
//	}
//
//}
