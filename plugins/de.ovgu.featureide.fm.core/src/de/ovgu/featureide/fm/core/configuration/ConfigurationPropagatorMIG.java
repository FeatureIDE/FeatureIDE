///* FeatureIDE - A Framework for Feature-Oriented Software Development
// * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
// * See http://www.fosd.de/featureide/ for further information.
// */
//package de.ovgu.featureide.fm.core.configuration;
//
//import java.util.ArrayList;
//import java.util.Collection;
//import java.util.Collections;
//import java.util.HashSet;
//import java.util.List;
//
//import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
//import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
//import de.ovgu.featureide.fm.core.analysis.cnf.analysis.ConditionallyCoreDeadAnalysisMIG;
//import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
//import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
//import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;
//import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
//import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
//import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
//
///**
// * Updates a configuration.
// *
// * @author Sebastian Krieter
// */
//public class ConfigurationPropagatorMIG extends ConfigurationPropagator {
//
//	public class UpdateMethod extends ConfigurationPropagator.UpdateMethod {
//
//		public UpdateMethod(boolean redundantManual) {
//			super(redundantManual, null);
//		}
//
//		public UpdateMethod(boolean redundantManual, List<SelectableFeature> featureOrder) {
//			super(redundantManual, featureOrder);
//		}
//
//		@Override
//		public Collection<SelectableFeature> execute(IMonitor<Collection<SelectableFeature>> workMonitor) {
//			if (formula == null) {
//				return false;
//			}
//			configuration.resetAutomaticValues();
//
//			final CNF rootNode = formula.getCNF();
//			final ArrayList<Integer> manualLiterals = new ArrayList<>();
//			for (final SelectableFeature feature : featureOrder) {
//				if ((feature.getManual() != Selection.UNDEFINED) && (includeAbstractFeatures || feature.getFeature().getStructure().isConcrete())) {
//					manualLiterals.add(rootNode.getVariables().getVariable(feature.getFeature().getName(), feature.getManual() == Selection.SELECTED));
//				}
//			}
//			final HashSet<Integer> manualLiteralSet = new HashSet<>(manualLiterals);
//			for (final SelectableFeature feature : configuration.getFeatures()) {
//				if ((feature.getManual() != Selection.UNDEFINED) && (includeAbstractFeatures || feature.getFeature().getStructure().isConcrete())) {
//					final Integer l = rootNode.getVariables().getVariable(feature.getFeature().getName(), feature.getManual() == Selection.SELECTED);
//					if (manualLiteralSet.add(l)) {
//						manualLiterals.add(l);
//					}
//				}
//			}
//
//			workMonitor.setRemainingWork(manualLiterals.size() + 1);
//			Collections.reverse(manualLiterals);
//
//			final ConditionallyCoreDeadAnalysisMIG analysis = new ConditionallyCoreDeadAnalysisMIG(rootNode, graph);
//			final int[] intLiterals = new int[manualLiterals.size()];
//			for (int i = 0; i < intLiterals.length; i++) {
//				intLiterals[i] = manualLiterals.get(i);
//			}
//			analysis.setAssumptions(new LiteralSet(intLiterals));
//			final LiteralSet impliedFeatures = LongRunningWrapper.runMethod(analysis, workMonitor.subTask(1));
//
//			// if there is a contradiction within the configuration
//			if (impliedFeatures == null) {
//				return false;
//			}
//
//			for (final int i : impliedFeatures.getLiterals()) {
//				final SelectableFeature feature = configuration.getSelectableFeature(rootNode.getVariables().getName(i));
//				configuration.setAutomatic(feature, i > 0 ? Selection.SELECTED : Selection.UNSELECTED);
//				workMonitor.invoke(feature);
//				manualLiteralSet.add(feature.getManual() == Selection.SELECTED ? i : -i);
//			}
//			// only for update of configuration editor
//			for (final SelectableFeature feature : configuration.getFeatures()) {
//				if (!manualLiteralSet
//						.contains(rootNode.getVariables().getVariable(feature.getFeature().getName(), feature.getManual() == Selection.SELECTED))) {
//					workMonitor.invoke(feature);
//				}
//			}
//
//			if (redundantManual) {
//				final AdvancedSatSolver solver = getSolver(true);
//				if (solver == null) {
//					return false;
//				}
//				for (final int feature : intLiterals) {
//					solver.assignmentPush(feature);
//				}
//
//				int literalCount = intLiterals.length;
//				for (int i = 0; i < solver.getAssignmentSize(); i++) {
//					final int oLiteral = intLiterals[i];
//					final SelectableFeature feature = configuration.getSelectableFeature(rootNode.getVariables().getName(oLiteral));
//					solver.assignmentSet(i, -oLiteral);
//					final SatResult satResult = solver.hasSolution();
//					switch (satResult) {
//					case FALSE:
//						configuration.setAutomatic(feature, oLiteral > 0 ? Selection.SELECTED : Selection.UNSELECTED);
//						workMonitor.invoke(feature);
//						intLiterals[i] = intLiterals[--literalCount];
//						solver.assignmentDelete(i--);
//						break;
//					case TIMEOUT:
//					case TRUE:
//						solver.assignmentSet(i, oLiteral);
//						workMonitor.invoke(feature);
//						break;
//					default:
//						throw new AssertionError(satResult);
//					}
//					workMonitor.worked();
//				}
//			}
//			return true;
//		}
//
//	}
//
//	private final ModalImplicationGraph graph;
//
//	public ConfigurationPropagatorMIG(FeatureModelFormula formula, ModalImplicationGraph graph, Configuration configuration, boolean includeAbstractFeatures) {
//		super(formula, configuration, includeAbstractFeatures);
//		this.graph = graph;
//	}
//
//	/**
//	 * This method creates a clone of the given {@link ConfigurationPropagatorMIG}
//	 *
//	 * @param configuration The new configuration object
//	 */
//	ConfigurationPropagatorMIG(ConfigurationPropagatorMIG oldPropagator, Configuration configuration) {
//		super(oldPropagator, configuration);
//		graph = oldPropagator.graph;
//	}
//
//	public ConfigurationPropagatorMIG(FeatureModelFormula formula, ModalImplicationGraph graph, Configuration configuration) {
//		this(formula, graph, configuration, true);
//	}
//
//	@Override
//	public UpdateMethod update(boolean redundantManual, List<SelectableFeature> featureOrder) {
//		return new UpdateMethod(redundantManual, featureOrder);
//	}
//
//	@Override
//	public UpdateMethod update(boolean redundantManual) {
//		return update(redundantManual, null);
//	}
//
//	@Override
//	public UpdateMethod update() {
//		return update(false, null);
//	}
//
//	@Override
//	protected ConfigurationPropagatorMIG clone(Configuration configuration) {
//		return new ConfigurationPropagatorMIG(this, configuration);
//	}
//
//}
