/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.CalcThread2;
import de.ovgu.featureide.fm.core.configuration.IConfigurationPropagator;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class ConfigurationChanger implements IConfigurationChanger, IConfigurationPropagator {

	private final FeatureModel featureModel;
	private final FeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final ConfigurationFG c;
	private Node node;

	private byte[] lastComputedValues;
	private final List<String> changedFeatures = new ArrayList<>();

	private CalcThread2 calcThread;
	private SatSolver satSolver1 = null;
	private SatSolver satSolver2 = null;

	private boolean initialized = false;

	public ConfigurationChanger(FeatureModel featureModel, VariableConfiguration variableConfiguration, ConfigurationFG c) {
		this.featureModel = featureModel;
		this.featureGraph = featureModel.getFeatureGraph();
		this.variableConfiguration = variableConfiguration;
		this.c = c;
		LongRunningJob.runMethod(load());
	}

	public class LoadMethod implements LongRunningMethod<Void> {
		@Override
		public Void execute(WorkMonitor monitor) {
			if (!initialized) {
				lastComputedValues = new byte[variableConfiguration.size()];
				Arrays.fill(lastComputedValues, (byte) Variable.UNDEFINED);
				node = NodeCreator.createNodes(featureModel, true).toCNF();
				calcThread = new CalcThread2(featureGraph.featureArray, ConfigurationChanger.this, node);
				initialized = true;
			}
			return null;
		}
	}

	public class CanBeValidMethod implements LongRunningMethod<Boolean> {
		@Override
		public Boolean execute(WorkMonitor monitor) {
			return sat(getCurrentLiterals(true));
		}
	}

	public class IsValidMethod implements LongRunningMethod<Boolean> {
		@Override
		public Boolean execute(WorkMonitor monitor) {
			return sat(getCurrentLiterals(false));
		}
	}

	public class GetSolutionsMethod implements LongRunningMethod<LinkedList<List<String>>> {
		private final int max;

		public GetSolutionsMethod(int max) {
			this.max = max;
		}

		@Override
		public LinkedList<List<String>> execute(WorkMonitor monitor) throws TimeoutException {
			SatSolver satSolver3 = new SatSolver(node, 1000, false);
			return satSolver3.getSolutionFeatures(getCurrentLiterals(true), max);
		}
	}

	public class CountSolutionsMethod implements LongRunningMethod<Long> {
		@Override
		public Long execute(WorkMonitor monitor) {
			if (satSolver2 == null) {
				satSolver2 = new SatSolver(node, 1000, false);
			}
			return satSolver2.countSolutions(getCurrentLiterals(true));
		}
	}

	public class LeadToValidConfiguration implements LongRunningMethod<Void> {
		@Override
		public Void execute(WorkMonitor monitor) {
			return null;
		}
	}

	public class UpdateMethod implements LongRunningMethod<List<String>> {
		@Override
		public List<String> execute(WorkMonitor monitor) {
			final boolean[] featureToCompute = new boolean[variableConfiguration.size()];
			changedFeatures.clear();
			for (int index = 0; index < lastComputedValues.length; index++) {
				final int oldValue = lastComputedValues[index];
				final int newValue = variableConfiguration.getVariable(index).getValue();
				if (newValue != oldValue) {
					lastComputedValues[index] = (byte) newValue;

					for (int i = 0; i < featureGraph.getSize(); i++) {
						if (i != index) {
							final int curValue = variableConfiguration.getVariable(i).getAutomaticValue();
							if (newValue != Variable.UNDEFINED) {
								if (curValue == Variable.UNDEFINED) {
									final byte edgeValue = featureGraph.getValue(index, i, newValue == Variable.TRUE);
									switch (edgeValue) {
									case FeatureGraph.VALUE_0:
										setNewValue(i, Variable.FALSE, false);
										featureToCompute[i] = false;
										break;
									case FeatureGraph.VALUE_1:
										setNewValue(i, Variable.TRUE, false);
										featureToCompute[i] = false;
										break;
									case FeatureGraph.VALUE_Q:
										featureToCompute[i] = true;
										break;
									case FeatureGraph.VALUE_NONE:
										if (oldValue != Variable.UNDEFINED
												&& featureGraph.getValue(index, i, oldValue == Variable.TRUE) != FeatureGraph.VALUE_NONE) {
											featureToCompute[i] = true;
										}
										break;
									default:
										continue;
									}
								}
							} else {
								if (curValue != Variable.UNDEFINED) {
									if (featureGraph.getValue(index, i, oldValue == Variable.TRUE) != FeatureGraph.VALUE_NONE) {
										featureToCompute[i] = true;
									}
								}
							}
						}
					}
				}
			}
			final List<Integer> compList = new ArrayList<>();

			// TODO Recursion for found values
			for (int i = 0; i < featureToCompute.length; i++) {
				if (featureToCompute[i]) {
					final LinkedList<Expression> varExpList = featureGraph.getExpListAr().get(i);
					if (varExpList == null || varExpList.isEmpty()) {
						compList.add(i);
						continue;
					}

					final int oldManualValue = variableConfiguration.getVariable(i).getManualValue();
					int newAutomaticValue = Variable.UNDEFINED;

					for (Expression expression : varExpList) {
						if (oldManualValue != Variable.TRUE && testExpression(expression, i, Variable.TRUE)) {
							newAutomaticValue = Variable.FALSE;
							break;
						}
						if (oldManualValue != Variable.FALSE && testExpression(expression, i, Variable.FALSE)) {
							newAutomaticValue = Variable.TRUE;
							break;
						}
					}

					variableConfiguration.setVariable(i, oldManualValue, true);
					if (newAutomaticValue != Variable.UNDEFINED) {
						setNewValue(i, newAutomaticValue, false);
						featureToCompute[i] = false;
					} else {
						compList.add(i);
					}
				}
			}

			if (!compList.isEmpty()) {
				final List<Literal> knownLiterals = new ArrayList<>();

				int i = 0;
				for (Variable var : variableConfiguration) {
					// TODO only if undefined
					switch (var.getManualValue()) {
					case Variable.TRUE:
						knownLiterals.add(new Literal(featureGraph.featureArray[i], true));
						break;
					case Variable.FALSE:
						knownLiterals.add(new Literal(featureGraph.featureArray[i], false));
						break;
					default:
						break;
					}
					i++;
				}

				calcThread.setKnownLiterals(knownLiterals);
				calcThread.addObjects(compList);
				calcThread.start();
			}

			if (c != null) {
				for (SelectableFeature f : c.getFeatures()) {
					final int index = featureGraph.getFeatureIndex(f.getName());
					if (index >= 0) {
						final int auto = variableConfiguration.getVariable(index).getAutomaticValue();
						final int manu = variableConfiguration.getVariable(index).getManualValue();
						f.setAutomatic(auto == Variable.UNDEFINED ? Selection.UNDEFINED : auto == Variable.TRUE ? Selection.SELECTED : Selection.UNSELECTED);
						f.setManual(manu == Variable.UNDEFINED ? Selection.UNDEFINED : manu == Variable.TRUE ? Selection.SELECTED : Selection.UNSELECTED);
						monitor.invoke(f);
					} else {
						if (Arrays.binarySearch(featureGraph.coreFeatures, f.getName()) >= 0) {
							f.setAutomatic(Selection.SELECTED);
							f.setManual(Selection.UNDEFINED);
							monitor.invoke(f);
						} else {
							if (Arrays.binarySearch(featureGraph.deadFeatures, f.getName()) >= 0) {
								f.setAutomatic(Selection.UNSELECTED);
								f.setManual(Selection.UNDEFINED);
								monitor.invoke(f);
							}
						}
					}
				}
			}

			Collections.sort(changedFeatures);
			return getChangedFeatures();
		}

	}

	@Override
	public CanBeValidMethod canBeValid() {
		return new CanBeValidMethod();
	}

	@Override
	public IsValidMethod isValid() {
		return new IsValidMethod();
	}

	@Override
	public GetSolutionsMethod getSolutions(int max) throws TimeoutException {
		return new GetSolutionsMethod(max);
	}

	@Override
	public CountSolutionsMethod number(long timeout) {
		return new CountSolutionsMethod();
	}

	@Override
	public UpdateMethod update(boolean redundantManual, String startFeatureName) {
		return new UpdateMethod();
	}

	@Override
	public IsValidMethod isValidNoHidden() {
		return new IsValidMethod();
	}

	private Literal[] getCurrentLiterals(boolean definedVariablesOnly) {
		final Literal[] literals = new Literal[variableConfiguration.size(definedVariablesOnly)];
		int i = 0;
		for (Variable var : variableConfiguration) {
			if (!definedVariablesOnly || var.getValue() != Variable.UNDEFINED) {
				literals[i++] = new Literal(featureGraph.featureArray[var.getId()], var.getValue() == Variable.TRUE);
			}
		}
		return literals;
	}

	private boolean sat(final Literal[] literals) {
		if (satSolver1 == null) {
			satSolver1 = new SatSolver(node, 1000, false);
		}
		try {
			return satSolver1.isSatisfiable(literals);
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
			return false;
		}
	}

	private boolean testExpression(Expression expression, int index, int value) {
		variableConfiguration.setVariable(index, value, true);
		expression.updateValue();
		return (expression.getValue() == Variable.FALSE);
	}

	public void setNewValue(int index, int value, boolean manual) {
		if (!manual) {
			lastComputedValues[index] = (byte) value;
		}

		//		addChangedFeature(featureGraph.featureArray[index] + ": " + (value == Variable.UNDEFINED ? "UNDEFINED" : (value == Variable.TRUE)));		
		if (value != Variable.UNDEFINED && variableConfiguration.getVariable(index).getValue() == Variable.UNDEFINED) {
			addChangedFeature(featureGraph.featureArray[index] + ": " + (value == Variable.TRUE));
		}

		variableConfiguration.setVariable(index, value, manual);
	}

	private synchronized void addChangedFeature(String featureString) {
		changedFeatures.add(featureString);
	}

	public FeatureGraph getFeatureGraph() {
		return featureGraph;
	}

	public VariableConfiguration getVariableConfiguration() {
		return variableConfiguration;
	}

	public List<String> getChangedFeatures() {
		return Collections.unmodifiableList(changedFeatures);
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

}
