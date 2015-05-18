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
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.CalcThread4;
import de.ovgu.featureide.fm.core.conf.worker.ISatThread;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.conf.worker.base.ThreadPool;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * For evaluation purposes.
 * 
 * @author Sebastian Krieter
 */
public class SatConfChanger implements IConfigurationChanger {
	private final FeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final ThreadPool<Integer> dfsThread;

	public SatConfChanger(FeatureModel featureModel, FeatureGraph featureGraph, VariableConfiguration variableConfiguration) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.dfsThread = new ThreadPool<>(new CalcThread4(featureGraph, this, NodeCreator.createNodes(featureModel, true).toCNF()));
		dfsThread.reset();
	}

	private final ConcurrentLinkedQueue<String> changedFeatures = new ConcurrentLinkedQueue<>();

	public List<String> setFeature(Feature f, byte newValue) {
		if (newValue == Variable.UNDEFINED) {
			return Collections.emptyList();
		}
		changedFeatures.clear();

		final int index = featureGraph.getFeatureIndex(f.getName());
		set(index, newValue == Variable.TRUE);

		final List<Integer> compList = new ArrayList<>();
		final List<Node> knownLiterals = new ArrayList<>();

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
				compList.add(i);
				break;
			}
			i++;
		}

		dfsThread.reset();
		for (AWorkerThread<Integer> thread : dfsThread.getThreads()) {
			((ISatThread) thread).setKnownLiterals(knownLiterals);
		}
		dfsThread.addObjects(compList);
		dfsThread.run();

		final ArrayList<String> changedFeatures2 = new ArrayList<>(changedFeatures);
		Collections.sort(changedFeatures2);
		return changedFeatures2;
	}

	public void set(int index, boolean value) {
		if (variableConfiguration.getVariable(index).getValue() == Variable.UNDEFINED) {
			variableConfiguration.setVariable(index, value ? Variable.TRUE : Variable.FALSE);
			changedFeatures.add(featureGraph.featureArray[index] + ": " + value);
		}
	}

}
