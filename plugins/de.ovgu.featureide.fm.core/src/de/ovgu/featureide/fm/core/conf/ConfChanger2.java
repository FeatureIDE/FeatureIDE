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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.worker.CalcThread3;
import de.ovgu.featureide.fm.core.conf.worker.ISatThread;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.conf.worker.base.ThreadPool;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class ConfChanger2 implements IConfigurationChanger {
	private final FeatureGraph featureGraph;
	private final VariableConfiguration variableConfiguration;
	private final ThreadPool<Integer> dfsThread;

	private final ConcurrentLinkedQueue<Variable> q = new ConcurrentLinkedQueue<>();

	private final HashSet<String> changedFeatures = new HashSet<>();
	private final HashSet<Integer> compList = new HashSet<>();
	private final byte[] known;
	private final int[] count = new int[5];

	public ConfChanger2(FeatureModel featureModel, FeatureGraph featureGraph, VariableConfiguration variableConfiguration) {
		this.featureGraph = featureGraph;
		this.known = new byte[featureGraph.getSize()];
		this.variableConfiguration = variableConfiguration;
		this.dfsThread = new ThreadPool<>(new CalcThread3(featureGraph, this, NodeCreator.createNodes(featureModel, true).toCNF()), null);
		dfsThread.reset();
	}

	public List<String> setFeature(Feature f, byte newValue) {
		if (newValue == Variable.UNDEFINED) {
			//TODO
			return Collections.emptyList();
		}

		compList.clear();
		q.clear();
		changedFeatures.clear();
		Arrays.fill(count, 0);
		Arrays.fill(known, (byte) 0);

		for (Variable var : variableConfiguration) {
			if (var.getValue() != Variable.UNDEFINED) {
				count[0]++;
			}
		}

		final int index = featureGraph.getFeatureIndex(f.getName());
		q.offer(new Variable(index, newValue));
		while (!q.isEmpty()) {
			Variable v = q.poll();
			setFeature_rec(v.getId(), v.getValue() == Variable.TRUE);
			count[2] += compList.size();
			sat();
		}

		//		setFeature_rec(index, newValue == Variable.TRUE);
		//		while (!compList.isEmpty()) {
		//			count[2] += compList.size();
		//			x(compList);
		//		}

		//		count[3] = featureGraph.getSize() - (count[0] + count[1] + count[2] + count[4]);
		//		System.out.println();
		//		System.out.println("Known:      " + count[0]);
		//		System.out.println("Unaffected: " + count[3]);
		//		System.out.println("Graph:      " + count[1]);
		//		System.out.println("Expression: " + count[4]);
		//		System.out.println("Sat:        " + count[2]);

		final List<String> ret = new ArrayList<>(changedFeatures);
		Collections.sort(ret);
		return ret;
	}

	public void setFeature_rec(int index, boolean value) {
		if (known[index] == 2 || variableConfiguration.getVariable(index).getValue() != Variable.UNDEFINED) {
			return;
		}
		set(index, value);

		if (value) {
			for (int i = 0; i < featureGraph.getSize(); i++) {
				if (known[i] == 2 || variableConfiguration.getVariable(i).getValue() != Variable.UNDEFINED) {
					known[i] = 2;
					continue;
				}
				final byte edge = (byte) (featureGraph.getEdge(index, i) & FeatureGraph.MASK_1_00001100);
				switch (edge) {
				case FeatureGraph.EDGE_10:
					set(i, false);
					count[1]++;
					break;
				case FeatureGraph.EDGE_11:
					set(i, true);
					count[1]++;
					break;
				case FeatureGraph.EDGE_1q:
					compList.add(i);
//										known[i] = 1;
					break;
				default:
					break;
				}
			}
		} else {
			for (int i = 0; i < featureGraph.getSize(); i++) {
				if (known[i] == 2 || variableConfiguration.getVariable(i).getValue() != Variable.UNDEFINED) {
					known[i] = 2;
					continue;
				}
				final byte edge = (byte) (featureGraph.getEdge(index, i) & FeatureGraph.MASK_0_00110000);
				switch (edge) {
				case FeatureGraph.EDGE_00:
					set(i, false);
					count[1]++;
					break;
				case FeatureGraph.EDGE_01:
					set(i, true);
					count[1]++;
					break;
				case FeatureGraph.EDGE_0q:
					compList.add(i);
//										known[i] = 1;
					break;
				default:
					break;
				}
			}
		}

		for (Iterator<Integer> it = compList.iterator(); it.hasNext();) {
			final int i = it.next();
			final List<Expression> varExpList = featureGraph.getExpListAr().get(i);
			if (varExpList == null || varExpList.isEmpty()) {
				continue;
			}
			for (Expression expression : varExpList) {
				variableConfiguration.setVariable(i, Variable.TRUE);
				expression.updateValue();
				if (expression.getValue() == Variable.FALSE) {
					variableConfiguration.setVariable(i, Variable.UNDEFINED);
					it.remove();
					q.offer(new Variable(i, Variable.TRUE));
					count[4]++;
					break;
				} else {
					variableConfiguration.setVariable(i, Variable.FALSE);
					expression.updateValue();
					if (expression.getValue() == Variable.FALSE) {
						variableConfiguration.setVariable(i, Variable.UNDEFINED);
						it.remove();
						q.offer(new Variable(i, Variable.TRUE));
						count[4]++;
						break;
					} else {
						variableConfiguration.setVariable(i, Variable.UNDEFINED);
					}
				}
			}
		}
	}

	public void x(int index, byte value) {
		if (value == Variable.UNDEFINED) {
			known[index] = 2;
		} else {
			q.offer(new Variable(index, value));
		}
	}

	private void sat() {
		if (compList.isEmpty()) {
			return;
		}
		final List<Node> knownLiterals = new ArrayList<>();
		for (Variable var : variableConfiguration) {
			switch (var.getValue()) {
			case Variable.TRUE:
				knownLiterals.add(new Literal(featureGraph.featureArray[var.getId()], true));
				break;
			case Variable.FALSE:
				knownLiterals.add(new Literal(featureGraph.featureArray[var.getId()], false));
				break;
			default:
				break;
			}
		}

		dfsThread.reset();
		for (AWorkerThread<Integer> thread : dfsThread.getThreads()) {
			((ISatThread) thread).setKnownLiterals(knownLiterals);
		}
		dfsThread.addObjects(compList);
		compList.clear();
		dfsThread.run();
	}

	private void set(int index, boolean value) {
		variableConfiguration.setVariable(index, value ? Variable.TRUE : Variable.FALSE);
		known[index] = 2;
		compList.remove(index);
		changedFeatures.add(featureGraph.featureArray[index] + ": " + value);
	}

}
