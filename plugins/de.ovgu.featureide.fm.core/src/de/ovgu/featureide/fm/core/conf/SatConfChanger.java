/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.prop4j.Literal;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.SatCalcThread;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * For evaluation purposes.
 * 
 * @author Sebastian Krieter
 */
public class SatConfChanger implements IConfigurationChanger {
	private final IFeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final SatCalcThread calcThread;
	private final IFeatureModel featureModel;

	public SatConfChanger(IFeatureModel featureModel, IFeatureGraph featureGraph, VariableConfiguration variableConfiguration) {
		this.featureModel = featureModel;
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.calcThread = new SatCalcThread(featureGraph, this, AdvancedNodeCreator.createCNF(featureModel));
	}

	private final ConcurrentLinkedQueue<String> changedFeatures = new ConcurrentLinkedQueue<>();

	private IFeature f = null;
	private int newValue = 0;

	public class UpdateMethod implements LongRunningMethod<List<String>> {
		@Override
		public List<String> execute(IMonitor monitor) {
			if (newValue == Variable.UNDEFINED) {
				return Collections.emptyList();
			}
			changedFeatures.clear();

			final int index = featureGraph.getFeatureIndex(f.getName());
			variableConfiguration.setVariable(index, newValue, true);
			changedFeatures.add(featureGraph.getFeatureArray()[index] + ": " + (newValue == Variable.TRUE));

			final List<Integer> compList = new ArrayList<>();
			final List<Literal> knownLiterals = new ArrayList<>();

			variableConfiguration.setVariable(index, Variable.UNDEFINED, true);

			int i = 0;
			for (Variable var : variableConfiguration) {
				switch (var.getValue()) {
				case Variable.TRUE:
					knownLiterals.add(new Literal(featureGraph.getFeatureArray()[i], true));
					break;
				case Variable.FALSE:
					knownLiterals.add(new Literal(featureGraph.getFeatureArray()[i], false));
					break;
				default:
					compList.add(i);
					break;
				}
				i++;
			}
			variableConfiguration.setVariable(index, newValue, true);

			calcThread.setKnownLiterals(knownLiterals, new Literal(featureGraph.getFeatureArray()[index], newValue == Variable.TRUE));
			calcThread.addObjects(compList);
			calcThread.start();

			final ArrayList<String> changedFeatures2 = new ArrayList<>(changedFeatures);
			Collections.sort(changedFeatures2);
			return changedFeatures2;
		}
	}

	public void setNewValue(int index, int value, boolean manual) {
		if (manual) {
			f = featureModel.getFeature(featureGraph.getFeatureArray()[index]);
			newValue = value;
		} else {
			if (value != Variable.UNDEFINED && variableConfiguration.getVariable(index).getValue() == Variable.UNDEFINED) {
				variableConfiguration.setVariable(index, value, false);
				changedFeatures.add(featureGraph.getFeatureArray()[index] + ": " + (value == Variable.TRUE));
			}
		}
	}

	@Override
	public UpdateMethod update(boolean redundantManual, String startFeatureName) {
		return new UpdateMethod();
	}

	@Override
	public void reset() {
	}

}
