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

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

public class FeatureGraphStatisticJob extends AProjectJob<FeatureGraphStatisticJob.Arguments> {

	public static class Arguments extends JobArguments {
		private final FeatureModel featureModel;

		public Arguments(FeatureModel featureModel) {
			super(Arguments.class);
			this.featureModel = featureModel;
		}
	}

	private FeatureGraph featureGraph;

	private long curTime = 0;
	private boolean wrongResult = false;

	protected FeatureGraphStatisticJob(Arguments arguments) {
		super("Computing Statistics on Feature Graph", arguments);
	}

	@Override
	protected boolean work() throws Exception {
		featureGraph = arguments.featureModel.getFeatureGraph();

		//		statisticPart(true, false);
		//		statisticPart(true, true);
		//		statisticPart2();

		try {
			statisticPart7();
			statisticPart8();
		} catch (IOException | CoreException e) {
			e.printStackTrace();
		}

		System.out.println();
		return true;
	}

	private static final boolean ALL_FEATURE = true;

	@SuppressWarnings("unused")
	private void statisticPart(boolean selected, boolean subtractReal) {
		final int[] featureNeigbors = new int[featureGraph.featureArray.length];
		int i = 0;
		for (String feature : featureGraph.featureArray) {
			if (ALL_FEATURE || arguments.featureModel.getFeature(feature).getChildren().size() == 0) {
				featureNeigbors[i++] = featureGraph.countNeighbors(feature, selected, subtractReal);
			}
		}

		Arrays.sort(featureNeigbors);
		for (int j = featureNeigbors.length - 1, end = featureNeigbors.length - i; j >= end; --j) {
			System.out.print(featureNeigbors[j] + ", ");
		}
		System.out.println();
	}

	@SuppressWarnings("unused")
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

	private void statisticPart7() throws IOException, CoreException {
		long startTime = System.nanoTime();
		curTime = startTime;
		statisticPart7_1(true, false);
		startTime = split(startTime);
		curTime = startTime;
		statisticPart7_1(false, false);
		startTime = split(startTime);
		curTime = startTime;
		statisticPart7_2(true, false);
		startTime = split(startTime);
		curTime = startTime;
		statisticPart7_2(false, false);
		split(startTime);
	}

	private void statisticPart8() throws IOException, CoreException {
		long startTime = System.nanoTime();
		curTime = startTime;
		statisticPart7_1(true, true);
		startTime = split(startTime);
		curTime = startTime;
		statisticPart7_1(false, true);
		startTime = split(startTime);
		curTime = startTime;
		statisticPart7_2(true, true);
		startTime = split(startTime);
		curTime = startTime;
		statisticPart7_2(false, true);
		split(startTime);
	}

	private void statisticPart7_1(boolean value, boolean compare) throws IOException, CoreException {
		final String fileName = "sat_single_" + value + ".txt";
		final IFile file = compare ? getFile(fileName) : createFile(fileName);
		if (file == null) {
			return;
		}
		final BufferedReader reader = compare ? new BufferedReader(new InputStreamReader(file.getContents(), Charset.availableCharsets().get("UTF-8"))) : null;
		final StringBuilder sb = compare ? null : new StringBuilder();
		final ArrayList<Integer> indexArray = createIndexArray();

		final VariableConfiguration variableConfiguration = new VariableConfiguration(featureGraph.getSize());
		final IConfigurationChanger c1 = compare ? new ConfChanger(arguments.featureModel, featureGraph, variableConfiguration) : new SatConfChanger(
				arguments.featureModel, featureGraph, variableConfiguration);

		for (int vIndex = 0; vIndex < featureGraph.getSize(); vIndex++) {
			if (compare) {
				read(value, reader.readLine(), indexArray, c1, vIndex);
			} else {
				write(value, sb, indexArray, c1, vIndex);
			}

			variableConfiguration.reset();
		}

		if (compare) {
			reader.close();
		} else {
			file.create(new ByteArrayInputStream(sb.toString().getBytes()), true, null);
		}
	}

	private void statisticPart7_2(boolean value, boolean compare) throws IOException, CoreException {
		final String fileName = "sat_stepwise_" + value + ".txt";
		final IFile file = compare ? getFile(fileName) : createFile(fileName);
		if (file == null) {
			return;
		}
		final BufferedReader reader = compare ? new BufferedReader(new InputStreamReader(file.getContents(), Charset.availableCharsets().get("UTF-8"))) : null;
		final StringBuilder sb = compare ? null : new StringBuilder();
		final ArrayList<Integer> indexArray = createIndexArray();

		final VariableConfiguration variableConfiguration = new VariableConfiguration(featureGraph.getSize());
		final IConfigurationChanger c1 = compare ? new ConfChanger(arguments.featureModel, featureGraph, variableConfiguration) : new SatConfChanger(
				arguments.featureModel, featureGraph, variableConfiguration);

		for (int vIndex = 0; vIndex < featureGraph.getSize();) {
			while (vIndex < featureGraph.getSize() && variableConfiguration.getVariable(indexArray.get(vIndex)).getValue() != Variable.UNDEFINED) {
				vIndex++;
			}
			if (vIndex < featureGraph.getSize()) {
				if (compare) {
					read(value, reader.readLine(), indexArray, c1, vIndex);
				} else {
					write(value, sb, indexArray, c1, vIndex);
				}
			}
		}

		if (compare) {
			reader.close();
		} else {
			file.create(new ByteArrayInputStream(sb.toString().getBytes()), true, null);
		}
	}

	private IFile getFile(final String fileName) {
		System.out.println();
		System.out.println("Comparing: " + fileName);
		wrongResult = false;
		return project.getFile(fileName);
	}

	private ArrayList<Integer> createIndexArray() {
		final ArrayList<Integer> indexArray = new ArrayList<>(featureGraph.getSize());
		workMonitor.setMaxAbsoluteWork(featureGraph.getSize());
		for (int i = 0; i < featureGraph.getSize(); i++) {
			indexArray.add(i);
		}
		return indexArray;
	}

	private IFile createFile(String fileName) throws CoreException {
		System.out.println();
		System.out.println("Writing: " + fileName);
		final IFile file = project.getFile(fileName);
		if (file.exists()) {
			System.out.print("Already existing - ");
			System.out.println("Skipping");
			return null;
		}
		return file;
	}

	private void write(boolean value, StringBuilder sb, ArrayList<Integer> indexArray, IConfigurationChanger c1, int vIndex) throws CoreException {
		final int index = indexArray.get(vIndex);
		final List<String> x = c1.setFeature(arguments.featureModel.getFeature(featureGraph.featureArray[index]), value ? Variable.TRUE : Variable.FALSE);
		final String result = x.toString() + "\n";
		sb.append(result);
		System.out.print(vIndex + " (" + index + ")");
		curTime = split(curTime);
	}

	private void read(boolean value, String satResult, ArrayList<Integer> indexArray, IConfigurationChanger c1, int vIndex) throws CoreException {
		if (vIndex < 0) {
			return;
		}
		final int index = indexArray.get(vIndex);
		final List<String> x = c1.setFeature(arguments.featureModel.getFeature(featureGraph.featureArray[index]), value ? Variable.TRUE : Variable.FALSE);
		final String result = x.toString();
		if (!result.equals(satResult)) {
			System.out.print("false | ");
			wrongResult = true;
		} else if (!wrongResult) {
			System.out.print("true | ");
		}
		System.out.print(vIndex + " (" + index + ")");
		curTime = split(curTime);
	}

	private long split(long start) {
		final long end = System.nanoTime();
		System.out.println(" -> " + Math.round((double) ((end - start)) / 1000000.0) / 1000.0 + "s");
		return System.nanoTime();
	}

}
