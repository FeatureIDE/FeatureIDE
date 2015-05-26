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
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.Literal;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.CalcThread2;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class ConfChanger implements IConfigurationChanger {

	private final FeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final CalcThread2 calcThread;

	private final List<String> changedFeatures = new ArrayList<>();

	public ConfChanger(FeatureModel featureModel, FeatureGraph featureGraph, VariableConfiguration variableConfiguration) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.calcThread = new CalcThread2(featureGraph, this, NodeCreator.createNodes(featureModel, true).toCNF());
	}

	//	private int[] count = new int[4];

	public List<String> setFeature(Feature f, int newValue) {
		final int index = featureGraph.getFeatureIndex(f.getName());
		final int oldValue = variableConfiguration.getVariable(index).getValue();

		if (newValue == oldValue) {
			return Collections.emptyList();
		}

		changedFeatures.clear();
		setNewValueManual(index, newValue);

		//		count = new int[4];

		final List<Integer> compList = new ArrayList<>();

		for (int i = 0; i < featureGraph.getSize(); i++) {
			if (i != index) {
				final int curValue = variableConfiguration.getVariable(i).getAutomaticValue();
				if (newValue != Variable.UNDEFINED) {
					if (curValue == Variable.UNDEFINED) {
						final byte edgeValue = featureGraph.getValue(index, i, newValue == Variable.TRUE);
						switch (edgeValue) {
						case FeatureGraph.VALUE_0:
							setNewValue(i, Variable.FALSE);
							break;
						case FeatureGraph.VALUE_1:
							setNewValue(i, Variable.TRUE);
							break;
						case FeatureGraph.VALUE_Q:
							compList.add(i);
							break;
						case FeatureGraph.VALUE_NONE:
							if (oldValue != Variable.UNDEFINED && featureGraph.getValue(index, i, oldValue == Variable.TRUE) != FeatureGraph.VALUE_NONE) {
								compList.add(i);
							}
							break;
						default:
							continue;
						}
					}
				} else {
					if (curValue != Variable.UNDEFINED) {
						if (featureGraph.getValue(index, i, oldValue == Variable.TRUE) != FeatureGraph.VALUE_NONE) {
							compList.add(i);
						}
					}
				}
			}
		}

		// TODO Recursion for found values
		for (Iterator<Integer> it = compList.iterator(); it.hasNext();) {
			final int i = it.next();

			final LinkedList<Expression> varExpList = featureGraph.getExpListAr().get(i);
			if (varExpList == null || varExpList.isEmpty()) {
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
				setNewValue(i, newAutomaticValue);
				it.remove();
			}
		}

		//		count[2] = compList.size();
		//		count[3] = featureGraph.getSize() - (count[0] + count[1] + count[2]);
		//		System.out.println();
		//		System.out.println("Known:      " + count[0]);
		//		System.out.println("Unaffected: " + count[3]);
		//		System.out.println("Non Sat:    " + count[1]);
		//		System.out.println("Sat:        " + count[2]);

		if (!compList.isEmpty()) {
			final List<Literal> knownLiterals = new ArrayList<>();

			variableConfiguration.setVariable(index, Variable.UNDEFINED, true);

			int i = 0;
			for (Variable var : variableConfiguration) {
				switch (var.getValue()) {
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
			variableConfiguration.setVariable(index, newValue, true);

			calcThread.setKnownLiterals(knownLiterals, new Literal(featureGraph.featureArray[index], newValue == Variable.TRUE));
			calcThread.addObjects(compList);
			calcThread.start();
		}

		Collections.sort(changedFeatures);
		return getChangedFeatures();
	}

	private boolean testExpression(Expression expression, int index, int value) {
		variableConfiguration.setVariable(index, value, true);
		expression.updateValue();
		return (expression.getValue() == Variable.FALSE);
	}

	public void setNewValue(int index, int value) {
		//		addChangedFeature(featureGraph.featureArray[index] + ": " + (value == Variable.UNDEFINED ? "UNDEFINED" : (value == Variable.TRUE)));
		if (value != Variable.UNDEFINED && variableConfiguration.getVariable(index).getValue() == Variable.UNDEFINED) {
			addChangedFeature(featureGraph.featureArray[index] + ": " + (value == Variable.TRUE));
		}
		variableConfiguration.setVariable(index, value, false);

	}

	private void setNewValueManual(int index, int value) {
		variableConfiguration.setVariable(index, value, true);
		addChangedFeature(featureGraph.featureArray[index] + ": " + (value == Variable.UNDEFINED ? "UNDEFINED" : (value == Variable.TRUE)));
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

}
