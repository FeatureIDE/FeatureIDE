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
package de.ovgu.featureide.fm.core.conf;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.SatSolver;
import org.prop4j.SatSolver.ValueType;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.GraphCalcThread;
import de.ovgu.featureide.fm.core.conf.worker.GraphCalcThread.CalcObject;
import de.ovgu.featureide.fm.core.configuration.IConfigurationPropagator;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Updates a configuration by using a feature graph.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationChanger implements IConfigurationChanger, IConfigurationPropagator {

	public class AutoCompletionMethod implements LongRunningMethod<Void> {

		private final int type;

		public AutoCompletionMethod(int type) {
			this.type = type;
		}

		@Override
		public Void execute(IMonitor monitor) {
			final UpdateHelper updateHelper = new UpdateHelper();
			for (int index = 0; index < featureGraph.getSize(); index++) {
				if (variableConfiguration.getVariable(index).getValue() != Variable.UNDEFINED) {
					continue;
				}

				final int newValue;
				switch (type) {
				case 0:
					newValue = Variable.FALSE;
					break;
				case 2:
					newValue = Math.random() < 0.5 ? Variable.FALSE : Variable.TRUE;
					break;
				case 1:
				default:
					newValue = Variable.TRUE;
					break;
				}
				setNewValue(index, newValue, true);

				updateHelper.init(index, newValue == Variable.TRUE);

				for (int i = index + 1; i < featureGraph.getSize(); i++) {
					updateHelper.updateVariable(i);
				}
			}
			return null;
		}
	}

	// TODO implement
	public class Resolve implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor workMonitor) throws Exception {
			return null;
		}
	}

	@Override
	public Resolve resolve() {
		return new Resolve();
	}

	public class CanBeValidMethod implements LongRunningMethod<Boolean> {

		@Override
		public Boolean execute(IMonitor monitor) {
			try {
				return sat(getCurrentLiterals(true));
			} catch (final Exception e) {
				Logger.logError(e);
				return false;
			}
		}
	}

	public class CountSolutionsMethod implements LongRunningMethod<Long> {

		@Override
		public Long execute(IMonitor monitor) {
			return new SatSolver(node, 1000, false).countSolutions(getCurrentLiterals(true));
		}
	}

	public class GetSolutionsMethod implements LongRunningMethod<List<List<String>>> {

		private final int max;

		public GetSolutionsMethod(int max) {
			this.max = max;
		}

		@Override
		public LinkedList<List<String>> execute(IMonitor monitor) throws TimeoutException {
			final SatSolver satSolver3 = new SatSolver(node, 1000, false);
			return satSolver3.getSolutionFeatures(getCurrentLiterals(true), max);
		}
	}

	public class IsValidMethod implements LongRunningMethod<Boolean> {

		@Override
		public Boolean execute(IMonitor monitor) {
			try {
				return sat(getCurrentLiterals(false));
			} catch (final Exception e) {
				Logger.logError(e);
				return false;
			}
		}
	}

	public class LeadToValidConfiguration implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor monitor) {
			return null;
		}
	}

	public class LoadMethod implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor monitor) {
			if (!isLoaded()) {
				lastComputedValues = new byte[variableConfiguration.size()];
				int i = 0;
				for (final Variable variable : variableConfiguration) {
					lastComputedValues[i++] = (byte) variable.getAutomaticValue();
				}
				node = AdvancedNodeCreator.createCNF(featureModel);
				calcThread = new GraphCalcThread(features, ConfigurationChanger.this, node);
				initialized = true;
			}
			return null;
		}
	}

	public class SimpleAutoCompletionMethod implements LongRunningMethod<Void> {

		private final boolean positive;

		public SimpleAutoCompletionMethod(boolean positive) {
			this.positive = positive;
		}

		@Override
		public Void execute(IMonitor monitor) {
			if (satSolver1 == null) {
				satSolver1 = new SatSolver(node, 1000, false);
			}
			final List<String> featureNames = satSolver1.getSolution(positive);
			for (final String featureName : featureNames) {
				final int index = featureGraph.getFeatureIndex(featureName);
				if (index >= 0) {
					setNewValue(featureGraph.getFeatureIndex(featureName), Variable.TRUE, false);
				}
			}

			for (int index = 0; index < featureGraph.getSize(); index++) {
				if (variableConfiguration.getVariable(index).getValue() == Variable.UNDEFINED) {
					setNewValue(index, Variable.FALSE, false);
				}
			}

			return null;
		}
	}

	public class UpdateMethod implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor monitor) {
			final byte[] featureToCompute = new byte[variableConfiguration.size()];
			boolean undefined = false;
			final List<Literal> knownLiterals = new ArrayList<>();
			for (int index = 0; index < lastComputedValues.length; index++) {

				final int oldValue = lastComputedValues[index];
				final int newValue = variableConfiguration.getVariable(index).getValue();

				if (newValue != oldValue) {

					lastComputedValues[index] = (byte) newValue;
					featureToCompute[index] = Variable.UNDEFINED;

					if (newValue == Variable.UNDEFINED) {
						undefined = true;
					} else {
						knownLiterals.add(new Literal(features[index], newValue == Variable.TRUE));
					}

					for (int i = 0; i < featureGraph.getSize(); i++) {
						if (i != index) {
							if (newValue != Variable.UNDEFINED) {
								final byte edgeValue = featureGraph.getValue(index, i, newValue == Variable.TRUE);
								switch (edgeValue) {
								case AFeatureGraph.VALUE_0:
									featureToCompute[i] = -Variable.FALSE;
									break;
								case AFeatureGraph.VALUE_1:
									featureToCompute[i] = -Variable.TRUE;
									break;
								case AFeatureGraph.VALUE_0Q:
									featureToCompute[i] = Variable.FALSE;
									break;
								case AFeatureGraph.VALUE_1Q:
									featureToCompute[i] = Variable.TRUE;
									break;
								case AFeatureGraph.VALUE_10Q:
									featureToCompute[i] = 3;
									break;
								case AFeatureGraph.VALUE_NONE:
									if ((oldValue != Variable.UNDEFINED)
										&& (featureGraph.getValue(index, i, oldValue == Variable.TRUE) != AFeatureGraph.VALUE_NONE)) {
										featureToCompute[i] = 3;
									}
									break;
								default:
									continue;
								}
							} else {
								if (featureGraph.getValue(index, i, oldValue == Variable.TRUE) != AFeatureGraph.VALUE_NONE) {
									featureToCompute[i] = 3;
								}
							}
						}
					}
				}
			}

			for (int index = 0; index < lastComputedValues.length; index++) {
				final byte b = featureToCompute[index];
				if (b < 0) {
					setNewValue(index, -b, false);
				}
			}

			final List<CalcObject> compList = new ArrayList<>();

			// TODO Recursion for found values
			for (int i = 0; i < featureToCompute.length; i++) {
				final byte computeFeature = featureToCompute[i];
				if (computeFeature > Variable.UNDEFINED) {
					final ValueType valueType;
					switch (computeFeature) {
					case Variable.FALSE:
						valueType = ValueType.FALSE;
						break;
					case Variable.TRUE:
						valueType = ValueType.TRUE;
						break;
					default:
						valueType = ValueType.ALL;
						break;
					}

					final Variable variable = variableConfiguration.getVariable(i);

					if (undefined) {
						if (variable.getAutomaticValue() != Variable.UNDEFINED) {
							compList.add(new CalcObject(i, valueType));
						}
					} else {
						if (variable.getAutomaticValue() == Variable.UNDEFINED) {
							compList.add(new CalcObject(i, valueType));
						}
					}
				}
			}

			if (!compList.isEmpty()) {
				int i = 0;
				if (undefined) {
					knownLiterals.clear();
					for (final Variable var : variableConfiguration) {
						switch (var.getManualValue()) {
						case Variable.TRUE:
							knownLiterals.add(new Literal(features[i], true));
							break;
						case Variable.FALSE:
							knownLiterals.add(new Literal(features[i], false));
							break;
						default:
							break;
						}
						i++;
					}
				} else {
					for (final Variable var : variableConfiguration) {
						switch (var.getAutomaticValue()) {
						case Variable.TRUE:
							knownLiterals.add(new Literal(features[i], true));
							break;
						case Variable.FALSE:
							knownLiterals.add(new Literal(features[i], false));
							break;
						default:
							break;
						}
						i++;
					}
				}

				calcThread.setKnownLiterals(knownLiterals);
				calcThread.addObjects(compList);
				calcThread.start();
			}

			if (c != null) {
				for (final SelectableFeature f : c.getFeatures()) {
					final int index = featureGraph.getFeatureIndex(f.getName());
					if (index >= 0) {
						final int auto = variableConfiguration.getVariable(index).getAutomaticValue();
						final int manu = variableConfiguration.getVariable(index).getManualValue();
						f.setAutomatic(auto == Variable.UNDEFINED ? Selection.UNDEFINED : auto == Variable.TRUE ? Selection.SELECTED : Selection.UNSELECTED);
						f.setManual(manu == Variable.UNDEFINED ? Selection.UNDEFINED : manu == Variable.TRUE ? Selection.SELECTED : Selection.UNSELECTED);
						monitor.invoke(f);
					} else {
						if (Arrays.binarySearch(coreFeatures, f.getName()) >= 0) {
							f.setAutomatic(Selection.SELECTED);
							f.setManual(Selection.UNDEFINED);
							monitor.invoke(f);
						} else {
							if (Arrays.binarySearch(deadFeatures, f.getName()) >= 0) {
								f.setAutomatic(Selection.UNSELECTED);
								f.setManual(Selection.UNDEFINED);
								monitor.invoke(f);
							}
						}
					}
				}
			}

			Collections.sort(changedFeatures);
			changedFeatures.clear();
			return null;
		}

	}

	public class UpdateNextMethod implements LongRunningMethod<Void> {

		@Override
		public Void execute(IMonitor monitor) {
			final UpdateHelper updateHelper = new UpdateHelper();
			for (int index = 0; index < lastComputedValues.length; index++) {
				final int newValue = variableConfiguration.getVariable(index).getValue();
				if (newValue != lastComputedValues[index]) {
					lastComputedValues[index] = (byte) newValue;

					updateHelper.init(index, newValue == Variable.TRUE);

					for (int i = (index + 1) % featureGraph.getSize(); i != index; i = (i + 1) % featureGraph.getSize()) {
						updateHelper.updateVariable(i);
					}
				}
			}
			return null;
		}
	}

	private class UpdateHelper {

		private Literal[] knownLiterals = null;

		private boolean undefined = false;

		private int variableIndex = 0;

		private boolean variableValue = false;

		public void init(int variableIndex, boolean variableValue) {
			this.variableIndex = variableIndex;
			this.variableValue = variableValue;

			undefined = false;

			knownLiterals = new Literal[variableConfiguration.size(true) + 1];

			int i = 0;
			for (final Variable var : variableConfiguration) {
				switch (var.getValue()) {
				case Variable.TRUE:
					knownLiterals[i++] = new Literal(features[var.getId()], true);
					break;
				case Variable.FALSE:
					knownLiterals[i++] = new Literal(features[var.getId()], false);
					break;
				default:
					break;
				}
			}
		}

		private boolean calc(int featureID) {
			final Literal curLiteral = new Literal(features[featureID], false);
			knownLiterals[knownLiterals.length - 1] = curLiteral;
			try {
				if (!sat(knownLiterals)) {
					setNewValue(featureID, Variable.TRUE, false);
				} else {
					curLiteral.flip();
					if (!sat(knownLiterals)) {
						setNewValue(featureID, Variable.FALSE, false);
					}
				}
			} catch (final TimeoutException e) {
				Logger.logError(e);
			}

			return variableConfiguration.getVariable(featureID).getValue() == Variable.UNDEFINED;
		}

		private boolean calcNegative(int featureID) {
			final Literal curLiteral = new Literal(features[featureID], true);
			knownLiterals[knownLiterals.length - 1] = curLiteral;
			try {
				if (!sat(knownLiterals)) {
					setNewValue(featureID, Variable.FALSE, false);
				}
			} catch (final TimeoutException e) {
				Logger.logError(e);
			}

			return variableConfiguration.getVariable(featureID).getValue() == Variable.UNDEFINED;
		}

		private boolean calcPositive(int featureID) {
			final Literal curLiteral = new Literal(features[featureID], false);
			knownLiterals[knownLiterals.length - 1] = curLiteral;
			try {
				if (!sat(knownLiterals)) {
					setNewValue(featureID, Variable.TRUE, false);
				}
			} catch (final TimeoutException e) {
				Logger.logError(e);
			}

			return variableConfiguration.getVariable(featureID).getValue() == Variable.UNDEFINED;
		}

		private void updateVariable(int index) {
			if (variableConfiguration.getVariable(index).getValue() == Variable.UNDEFINED) {
				final byte edgeValue = featureGraph.getValue(variableIndex, index, variableValue);
				switch (edgeValue) {
				case AFeatureGraph.VALUE_0:
					setNewValue(index, Variable.FALSE, false);
					break;
				case AFeatureGraph.VALUE_1:
					setNewValue(index, Variable.TRUE, false);
					break;
				case AFeatureGraph.VALUE_0Q:
					if (!undefined) {
						undefined = calcNegative(index);
					}
					break;
				case AFeatureGraph.VALUE_1Q:
					if (!undefined) {
						undefined = calcPositive(index);
					}
					break;
				case AFeatureGraph.VALUE_10Q:
				case AFeatureGraph.VALUE_NONE:
				default:
					if (!undefined) {
						undefined = calc(index);
					}
					break;
				}
			}
		}
	}

	private final ConfigurationFG c;

	private GraphCalcThread calcThread;

	private final List<String> changedFeatures = new ArrayList<>();

	private final IFeatureGraph featureGraph;

	private final IFeatureModel featureModel;

	private boolean initialized = false;

	private byte[] lastComputedValues;

	private Node node;

	private SatSolver satSolver1 = null;

	private final VariableConfiguration variableConfiguration;

	private final String[] coreFeatures, deadFeatures, features;

	public ConfigurationChanger(IFeatureGraph featureGraph, IFeatureModel featureModel, VariableConfiguration variableConfiguration, ConfigurationFG c) {
		this.featureModel = featureModel;
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.c = c;

		coreFeatures = FeatureUtils.getCoreFeaturesFromFeatureGraph(featureGraph);
		deadFeatures = FeatureUtils.getDeadFeaturesFromFeatureGraph(featureGraph);
		features = FeatureUtils.getFeaturesFromFeatureGraph(featureGraph);

		LongRunningWrapper.runMethod(load());
	}

	public AutoCompletionMethod autoCompletion(int type) {
		return new AutoCompletionMethod(type);
	}

	@Override
	public CanBeValidMethod canBeValid() {
		return new CanBeValidMethod();
	}

	@Override
	public LongRunningMethod<List<Node>> findOpenClauses(List<SelectableFeature> featureList) {
		return null;
	}

	public List<String> getChangedFeatures() {
		return Collections.unmodifiableList(changedFeatures);
	}

	public IFeatureGraph getFeatureGraph() {
		return featureGraph;
	}

	@Override
	public GetSolutionsMethod getSolutions(int max) throws TimeoutException {
		return new GetSolutionsMethod(max);
	}

	public VariableConfiguration getVariableConfiguration() {
		return variableConfiguration;
	}

	@Override
	public IsValidMethod isValid() {
		return new IsValidMethod();
	}

	@Override
	public IsValidMethod isValidNoHidden() {
		return new IsValidMethod();
	}

	@Override
	public LeadToValidConfiguration leadToValidConfiguration(List<SelectableFeature> featureList) {
		return new LeadToValidConfiguration();
	}

	@Override
	public LeadToValidConfiguration leadToValidConfiguration(List<SelectableFeature> featureList, int mode) {
		return new LeadToValidConfiguration();
	}

	@Override
	public LoadMethod load() {
		return new LoadMethod();
	}

	@Override
	public CountSolutionsMethod number(long timeout, boolean includeHiddenFeatures) {
		return new CountSolutionsMethod();
	}

	@Override
	public void reset() {
		Arrays.fill(lastComputedValues, (byte) Variable.UNDEFINED);
	}

	@Override
	public void setNewValue(int index, int value, boolean manual) {
		variableConfiguration.setVariable(index, value, manual);

		if (!manual) {
			lastComputedValues[index] = (byte) variableConfiguration.getVariable(index).getValue();
		}
	}

	public SimpleAutoCompletionMethod simpleAutoCompletion(boolean positive) {
		return new SimpleAutoCompletionMethod(positive);
	}

	@Override
	public UpdateMethod update(boolean redundantManual, List<SelectableFeature> featureOrder) {
		return new UpdateMethod();
	}

	@Override
	public LongRunningMethod<Void> update(boolean redundantManual) {
		return new UpdateMethod();
	}

	@Override
	public LongRunningMethod<Void> update() {
		return new UpdateMethod();
	}

	public UpdateNextMethod updateNext() {
		return new UpdateNextMethod();
	}

	private Literal[] getCurrentLiterals(boolean definedVariablesOnly) {
		final Literal[] literals = new Literal[variableConfiguration.size(definedVariablesOnly)];
		int i = 0;
		for (final Variable var : variableConfiguration) {
			if (!definedVariablesOnly || (var.getValue() != Variable.UNDEFINED)) {
				literals[i++] = new Literal(features[var.getId()], var.getValue() == Variable.TRUE);
			}
		}
		return literals;
	}

	private boolean sat(final Literal[] literals) throws TimeoutException {
		if (satSolver1 == null) {
			satSolver1 = new SatSolver(node, 1000, false);
		}
		return satSolver1.isSatisfiable(literals);
	}

	@Override
	public boolean isLoaded() {
		return initialized;
	}

}
