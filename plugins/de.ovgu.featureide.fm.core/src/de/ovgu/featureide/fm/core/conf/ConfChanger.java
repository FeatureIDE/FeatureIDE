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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.CalcThread;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.conf.worker.base.ThreadPool;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class ConfChanger {
	private final FeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final ThreadPool<Integer> dfsThread;

	private final List<Node> ls = new ArrayList<>();


	public ConfChanger(FeatureModel featureModel, FeatureGraph featureGraph, VariableConfiguration variableConfiguration) {
		this.featureGraph = featureGraph;
		this.variableConfiguration = variableConfiguration;
		this.dfsThread = new ThreadPool<>(new CalcThread(featureGraph, variableConfiguration, NodeCreator.createNodes(featureModel, false).toCNF()));
		dfsThread.reset();
	}

	public void setFeature(Feature f, byte newValue) {
		if (newValue == Variable.UNDEFINED) {
			return;
		}

		final int index = featureGraph.getFeatureIndex(f.getName());
		set(index, newValue == Variable.TRUE);

		List<Integer> compList = new ArrayList<>();

		if (newValue == Variable.TRUE) {
			for (int i = 0; i < featureGraph.getSize(); i++) {
				if (variableConfiguration.getVariable(i).getValue() != Variable.UNDEFINED) {
					continue;
				}
				final byte edge = (byte) (featureGraph.getEdge(index, i) & FeatureGraph.MASK_1_00001100);
				switch (edge) {
				case FeatureGraph.EDGE_10:
					set(i, false);
					break;
				case FeatureGraph.EDGE_11:
					set(i, true);
					break;
				case FeatureGraph.EDGE_1q:
					compList.add(i);
					continue;
				default:
					continue;
				}
			}
		} else {
			for (int i = 0; i < featureGraph.getSize(); i++) {
				if (variableConfiguration.getVariable(i).getValue() != Variable.UNDEFINED) {
					continue;
				}
				final byte edge = (byte) (featureGraph.getEdge(index, i) & FeatureGraph.MASK_0_00110000);
				switch (edge) {
				case FeatureGraph.EDGE_00:
					set(i, false);
					break;
				case FeatureGraph.EDGE_01:
					set(i, true);
					break;
				case FeatureGraph.EDGE_0q:
					compList.add(i);
					continue;
				default:
					continue;
				}
			}
		}

		for (Iterator<Integer> it = compList.iterator(); it.hasNext();) {
			final int i = it.next();
			final LinkedList<Expression> varExpList = featureGraph.getExpListAr().get(i);
			if (varExpList == null || varExpList.isEmpty()) {
				it.remove();
				continue;
			}
			for (Expression expression : varExpList) {
				variableConfiguration.setVariable(i, Variable.TRUE);
				expression.updateValue();
				if (expression.getValue() == Variable.FALSE) {
					variableConfiguration.setVariable(i, Variable.FALSE);
//					ls.add(new Literal(featureGraph.featureArray[i], false));
					it.remove();
					break;
				} else {
					variableConfiguration.setVariable(i, Variable.FALSE);
					expression.updateValue();
					if (expression.getValue() == Variable.FALSE) {
						variableConfiguration.setVariable(i, Variable.TRUE);
//						ls.add(new Literal(featureGraph.featureArray[i], true));
						it.remove();
						break;
					} else {
						variableConfiguration.setVariable(i, Variable.UNDEFINED);
					}
				}
			}
		}
		
		ls.clear();
		
		int i = 0;
		for (Variable var : variableConfiguration) {
			switch (var.getValue()) {
			case Variable.TRUE:
				ls.add(new Literal(featureGraph.featureArray[i], true));
				break;	
			case Variable.FALSE:
				ls.add(new Literal(featureGraph.featureArray[i], false));
				break;	
			default:
				break;				
			}
			i++;
		}
		
		//TODO vorher lösung suchen mit sat solver
		dfsThread.reset();
		for (AWorkerThread<Integer> thread : dfsThread.getThreads()) {
			((CalcThread) thread).setLs(ls);
		}
		dfsThread.addObkects(compList);
		dfsThread.run();

		//		for (Integer i : compList) {
		//			final int curIndex = ls.size();
		//			try {
		//				ls.add(new Literal(featureGraph.featureArray[i], false));
		//				if (!solver.isSatisfiable(ls)) {
		//					variableConfiguration.setVariable(i, Variable.TRUE);
		//					ls.set(curIndex, new Literal(featureGraph.featureArray[i], true));
		//				} else {
		//					ls.set(curIndex, new Literal(featureGraph.featureArray[i], true));
		//					if (!solver.isSatisfiable(ls)) {
		//						variableConfiguration.setVariable(i, Variable.FALSE);
		//						ls.set(curIndex, new Literal(featureGraph.featureArray[i], false));
		//					} else {
		//						ls.remove(curIndex);
		//					}
		//				}
		//			} catch (TimeoutException e) {
		//				FMCorePlugin.getDefault().logError(e);
		//				ls.remove(curIndex);
		//			}
		//		}
	}
	
	private void set(int index, boolean value) {
		if (variableConfiguration.getVariable(index).getValue() == Variable.UNDEFINED) {
			variableConfiguration.setVariable(index, value ? Variable.TRUE : Variable.FALSE);
//			ls.add(new Literal(featureGraph.featureArray[index], value));
		}
	}

}
