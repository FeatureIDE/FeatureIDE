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

import java.util.Arrays;

import de.ovgu.featureide.fm.core.FeatureModel;
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
		statisticPart(true, false);
		//		statisticPart(false, false);
		statisticPart(true, true);
		//		statisticPart(false, true);
		statisticPart2();
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
//				System.out.print(edge);
//				System.out.print(" ");
			}
			System.out.print(": ");
			System.out.println(feature);
		}
		System.out.println();
	}

}
