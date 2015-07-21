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
import org.prop4j.SatSolver.ValueType;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.GraphCalcThread;
import de.ovgu.featureide.fm.core.conf.worker.GraphCalcThread.CalcObject;
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
	private final IFeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final ConfigurationFG c;
	private Node node;

	private byte[] lastComputedValues;
	private final List<String> changedFeatures = new ArrayList<>();

	private GraphCalcThread calcThread;
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
		public Void run(WorkMonitor monitor) {
			if (!initialized) {
				lastComputedValues = new byte[variableConfiguration.size()];
				Arrays.fill(lastComputedValues, (byte) Variable.UNDEFINED);
				node = NodeCreator.createNodes(featureModel, true).toCNF();
				calcThread = new GraphCalcThread(featureGraph.getFeatureArray(), ConfigurationChanger.this, node);
				initialized = true;
			}
			return null;
		}
	}

	public class CanBeValidMethod implements LongRunningMethod<Boolean> {
		@Override
		public Boolean run(WorkMonitor monitor) {
			try {
				return sat(getCurrentLiterals(true));
			} catch (Exception e) {
				FMCorePlugin.getDefault().logError(e);
				return false;
			}
		}
	}

	public class IsValidMethod implements LongRunningMethod<Boolean> {
		@Override
		public Boolean run(WorkMonitor monitor) {
			try {
				return sat(getCurrentLiterals(false));
			} catch (Exception e) {
				FMCorePlugin.getDefault().logError(e);
				return false;
			}
		}
	}

	public class GetSolutionsMethod implements LongRunningMethod<LinkedList<List<String>>> {
		private final int max;

		public GetSolutionsMethod(int max) {
			this.max = max;
		}

		@Override
		public LinkedList<List<String>> run(WorkMonitor monitor) throws TimeoutException {
			SatSolver satSolver3 = new SatSolver(node, 1000, false);
			return satSolver3.getSolutionFeatures(getCurrentLiterals(true), max);
		}
	}

	public class CountSolutionsMethod implements LongRunningMethod<Long> {
		@Override
		public Long run(WorkMonitor monitor) {
			if (satSolver2 == null) {
				satSolver2 = new SatSolver(node, 1000, false);
			}
			return satSolver2.countSolutions(getCurrentLiterals(true));
		}
	}

	public class LeadToValidConfiguration implements LongRunningMethod<Void> {
		@Override
		public Void run(WorkMonitor monitor) {
			return null;
		}
	}

	public class UpdateMethod implements LongRunningMethod<List<String>> {
		@Override
		public List<String> run(WorkMonitor monitor) {
			final byte[] featureToCompute = new byte[variableConfiguration.size()];
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
									case AFeatureGraph.VALUE_0:
										setNewValue(i, Variable.FALSE, false);
										featureToCompute[i] = 0;
										break;
									case AFeatureGraph.VALUE_1:
										setNewValue(i, Variable.TRUE, false);
										featureToCompute[i] = 0;
										break;
									case AFeatureGraph.VALUE_0Q:
										featureToCompute[i] = 1;
										break;
									case AFeatureGraph.VALUE_1Q:
										featureToCompute[i] = 2;
										break;
									case AFeatureGraph.VALUE_10Q:
										featureToCompute[i] = 3;
										break;
									case AFeatureGraph.VALUE_NONE:
										if (oldValue != Variable.UNDEFINED
												&& featureGraph.getValue(index, i, oldValue == Variable.TRUE) != AFeatureGraph.VALUE_NONE) {
											featureToCompute[i] = 3;
										}
										break;
									default:
										continue;
									}
								}
							} else {
								if (curValue != Variable.UNDEFINED) {
									if (featureGraph.getValue(index, i, oldValue == Variable.TRUE) != AFeatureGraph.VALUE_NONE) {
										featureToCompute[i] = 3;
									}
								}
							}
						}
					}
				}
			}
			final List<CalcObject> compList = new ArrayList<>();

			// TODO Recursion for found values
			for (int i = 0; i < featureToCompute.length; i++) {
				final byte computeFeature = featureToCompute[i];
				if (computeFeature > 0) {
					final ValueType valueType;
					switch (computeFeature) {
					case 1:
						valueType = ValueType.FALSE;
						break;
					case 2:
						valueType = ValueType.TRUE;
						break;
					default:
						valueType = ValueType.ALL;
						break;
					}
					final LinkedList<Expression> varExpList = featureGraph.getExpListAr().get(i);
					if (varExpList == null || varExpList.isEmpty()) {
						compList.add(new CalcObject(i, valueType));
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
						featureToCompute[i] = 0;
					} else {
						compList.add(new CalcObject(i, valueType));
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
						knownLiterals.add(new Literal(featureGraph.getFeatureArray()[i], true));
						break;
					case Variable.FALSE:
						knownLiterals.add(new Literal(featureGraph.getFeatureArray()[i], false));
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
						if (Arrays.binarySearch(featureGraph.getCoreFeatures(), f.getName()) >= 0) {
							f.setAutomatic(Selection.SELECTED);
							f.setManual(Selection.UNDEFINED);
							monitor.invoke(f);
						} else {
							if (Arrays.binarySearch(featureGraph.getDeadFeatures(), f.getName()) >= 0) {
								f.setAutomatic(Selection.UNSELECTED);
								f.setManual(Selection.UNDEFINED);
								monitor.invoke(f);
							}
						}
					}
				}
			}

			Collections.sort(changedFeatures);
			final ArrayList<String> ret = new ArrayList<>(changedFeatures);
			changedFeatures.clear();
			return ret;
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

	public UpdateNextMethod updateNext() {
		return new UpdateNextMethod();
	}

	public AutoCompletionMethod autoCompletion(int type) {
		return new AutoCompletionMethod(type);
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
				literals[i++] = new Literal(featureGraph.getFeatureArray()[var.getId()], var.getValue() == Variable.TRUE);
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
			addChangedFeature(featureGraph.getFeatureArray()[index] + ": " + (value == Variable.TRUE));
		}

		variableConfiguration.setVariable(index, value, manual);
	}

	private synchronized void addChangedFeature(String featureString) {
		changedFeatures.add(featureString);
	}

	public IFeatureGraph getFeatureGraph() {
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

	@Override
	public void reset() {
		Arrays.fill(lastComputedValues, (byte) Variable.UNDEFINED);
	}

	private class UpdateHelper {

		private Literal[] knownLiterals = null;

		private boolean undefined = false;

		private boolean variableValue = false;

		private int variableIndex = 0;

		public void init(int variableIndex, boolean variableValue) {
			this.variableIndex = variableIndex;
			this.variableValue = variableValue;

			final List<Literal> knownLiteralList = new ArrayList<>();

			int i = 0;
			for (Variable var : variableConfiguration) {
				switch (var.getManualValue()) {
				case Variable.TRUE:
					knownLiteralList.add(new Literal(featureGraph.getFeatureArray()[i], true));
					break;
				case Variable.FALSE:
					knownLiteralList.add(new Literal(featureGraph.getFeatureArray()[i], false));
					break;
				default:
					break;
				}
				i++;
			}

			knownLiterals = knownLiteralList.toArray(new Literal[knownLiteralList.size() + 1]);
			undefined = false;
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
					if (!undefined) {
						undefined = calc(index);
					}
					break;
				case AFeatureGraph.VALUE_NONE:
				default:
					undefined = true;
					break;
				}
			}
		}

		private boolean calc(int featureID) {
			final Literal curLiteral = new Literal(featureGraph.getFeatureArray()[featureID], false);
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
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}

			return variableConfiguration.getVariable(featureID).getValue() == Variable.UNDEFINED;
		}

		private boolean calcPositive(int featureID) {
			final Literal curLiteral = new Literal(featureGraph.getFeatureArray()[featureID], false);
			knownLiterals[knownLiterals.length - 1] = curLiteral;
			try {
				if (!sat(knownLiterals)) {
					setNewValue(featureID, Variable.TRUE, false);
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}

			return variableConfiguration.getVariable(featureID).getValue() == Variable.UNDEFINED;
		}

		private boolean calcNegative(int featureID) {
			final Literal curLiteral = new Literal(featureGraph.getFeatureArray()[featureID], true);
			knownLiterals[knownLiterals.length - 1] = curLiteral;
			try {
				if (!sat(knownLiterals)) {
					setNewValue(featureID, Variable.FALSE, false);
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}

			return variableConfiguration.getVariable(featureID).getValue() == Variable.UNDEFINED;
		}
	}

	public class UpdateNextMethod implements LongRunningMethod<Void> {
		@Override
		public Void run(WorkMonitor monitor) {
			final UpdateHelper updateHelper = new UpdateHelper();
			for (int index = 0; index < lastComputedValues.length; index++) {
				final int newValue = variableConfiguration.getVariable(index).getValue();
				if (newValue != lastComputedValues[index]) {
					lastComputedValues[index] = (byte) newValue;

					updateHelper.init(index, newValue == Variable.TRUE);

					for (int i = index + 1; i != index; i = (i + 1) % featureGraph.getSize()) {
						updateHelper.updateVariable(i);
					}
				}
			}
			return null;
		}
	}

	public class AutoCompletionMethod implements LongRunningMethod<Void> {

		private final int type;

		public AutoCompletionMethod(int type) {
			this.type = type;
		}

		@Override
		public Void run(WorkMonitor monitor) {
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

}
