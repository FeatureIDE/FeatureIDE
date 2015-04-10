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

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.job.AStoppableJob;

public class FeatureGraphStatisticJob extends AStoppableJob {

	private final FeatureModel featureModel;
	private FeatureGraph featureGraph;

	public FeatureGraphStatisticJob(FeatureModel featureModel) {
		super("Spliting Feature Model");
		this.featureModel = featureModel;
	}

	@Override
	protected boolean work() throws Exception {
		featureGraph = featureModel.getFeatureGraph();
		statistic();

		return true;
	}

	private void statistic() {		
//		statisticPart(true, false);
//		statisticPart(true, true);
//		statisticPart2();
//		
//		statisticPart4();
//
//		statisticPart3(0);
//		statisticPart3(1);
//		statisticPart3(10);
//		for (int i = 50; i <= 600; i+= 50) {
//			statisticPart3(i);
//		}
		
		statisticPart5();
		
		System.out.println();
	}

	private static final boolean ALL_FEATURE = true;

	@SuppressWarnings("unused")
	private void statisticPart(boolean selected, boolean subtractReal) {
		final int[] featureNeigbors = new int[featureGraph.featureArray.length];
		int i = 0;
		for (String feature : featureGraph.featureArray) {
			if (ALL_FEATURE || featureModel.getFeature(feature).getChildren().size() == 0) {
				featureNeigbors[i++] = featureGraph.countNeighbors(feature, selected, subtractReal);
			}
		}

		Arrays.sort(featureNeigbors);
		for (int j = featureNeigbors.length - 1, end = featureNeigbors.length - i; j >= end; --j) {
			System.out.print(featureNeigbors[j] + ", ");
		}
		System.out.println();
	}
	
	private void statisticPart2() {
		System.out.println();
		for (String feature : featureGraph.featureArray) {
			for (String feature2 : featureGraph.featureArray) {
				final byte edge = featureGraph.getEdge(featureGraph.getFeatureIndex(feature), featureGraph.getFeatureIndex(feature2));
				if (FeatureGraph.isEdge(edge, FeatureGraph.EDGE_10) || FeatureGraph.isEdge(edge, FeatureGraph.EDGE_11)) {
					System.out.print("1");
				} else {
					System.out.print("0");
				}
			}
			System.out.print(": ");
			System.out.println(feature);
		}
		System.out.println();
	}
	
	private void statisticPart3(int blub) {
		final VariableConfiguration variableConfiguration = new VariableConfiguration(featureGraph.getSize());
		final ConfChanger c = new ConfChanger(featureModel, featureGraph, variableConfiguration);
		int vIndex = 0;
		for (int i = 0; i < blub; i++) {
			while (vIndex < featureGraph.getSize() && variableConfiguration.getVariable(vIndex).getValue() != Variable.UNDEFINED) {
				vIndex++;
			}
			if (vIndex < featureGraph.getSize()) {
				c.setFeature(featureModel.getFeature(featureGraph.featureArray[vIndex]), Variable.TRUE);
			}
		}
		
		int x = 0;
		for (int i = 0; i < featureGraph.getSize(); i++) {
			if (variableConfiguration.getVariable(i).getValue() != Variable.UNDEFINED) {
				x++;
			}
		}
		
		System.out.println();
		System.out.println(x);
	}
	
	private void statisticPart4() {
		int[] c = new int[featureGraph.getSize()];
		int i = 0;
		for (LinkedList<Expression> x : featureGraph.getExpListAr()) {
			c[i++] = (x == null) ? 0 : x.size();
		}
		Arrays.sort(c);
		for (int j = 0; j < c.length; j++) {
			System.out.println(c[j]);
		}
	}
	
	private void statisticPart5() {
		final ArrayList<Integer> indexArray = new ArrayList<>(featureGraph.getSize());
		for (int i = 0; i < featureGraph.getSize(); i++) {
			indexArray.add(i);
		}
		Collections.shuffle(indexArray);
		
		final long firstStart = System.nanoTime();
		long start = firstStart;
		
		final VariableConfiguration variableConfiguration = new VariableConfiguration(featureGraph.getSize());
		final ConfChanger c = new ConfChanger(featureModel, featureGraph, variableConfiguration);
		System.out.print("Create: ");
		start = split(start);
		
		for (int vIndex = 0; vIndex < featureGraph.getSize();) {
			while (vIndex < featureGraph.getSize() && variableConfiguration.getVariable(indexArray.get(vIndex)).getValue() != Variable.UNDEFINED) {
				vIndex++;
			}
			if (vIndex < featureGraph.getSize()) {
				c.setFeature(featureModel.getFeature(featureGraph.featureArray[indexArray.get(vIndex)]), Variable.TRUE);
				System.out.print(vIndex + ": ");
				start = split(start);
			}
		}
		
		System.out.println();
		start = split(firstStart);
	}
	
	private long split(long start) {
		final long end = System.nanoTime();
		System.out.println(Math.round((double)((end - start)) / 1000000.0) / 1000.0);
		return System.nanoTime();
	}

}
