/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl.job;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.job.util.AMonitorJob;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.mpl.signature.filter.ViewTagFilter;
import de.ovgu.featureide.core.mpl.util.NumberConverter;
import de.ovgu.featureide.core.mpl.util.SignatureGroup;

/**
 * Builds interfaces for a certain configuration.
 * 
 * @author Sebastian Krieter
 */
public class PrintConfigurationInterfacesJob extends AMonitorJob<PrintConfigurationInterfacesJob.Arguments> {
	
	public static class Arguments extends AJobArguments {
		public Arguments() {
			super(Arguments.class);
		}
	}
	
	protected PrintConfigurationInterfacesJob(Arguments arguments) {
		super("Build Configuration Interfaces", arguments);
	}

	@Override
	protected boolean work() {
		monitor.subTask("Calculate Solutions");
		
		final LinkedList<List<String>> solutionList;
		try {
			solutionList = interfaceProject.getConfiguration().getSolutions(interfaceProject.getConfigLimit());
		} catch (TimeoutException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		final int numberSolutions = solutionList.size();
		
		monitor.subTask("Generate Signatures");
		
		IFolder interfaceFolder = interfaceProject.getProjectReference().getFolder("configuration_interfaces");
		IFolder groupListFolder = interfaceFolder.getFolder("groups");
		try {
			if (interfaceFolder.exists()) {
				interfaceFolder.delete(true, null);
			}
			interfaceFolder.create(false, true, null);
			groupListFolder.create(false, true, null);
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		final HashMap<ProjectStructure, SignatureGroup> signatureMap = new HashMap<ProjectStructure, SignatureGroup>();
		final NumberConverter converter = new NumberConverter(numberSolutions);
		
		int solutionId = 0, groupId = 0;
		setMaxAbsoluteWork(numberSolutions);
		
		int[][] minNumbers = new int[2][3];
		int[][] solutionIds = new int[2][3];
		int[][] groupIds = new int[2][3];
		int[] minFeatures = new int[3];
		Arrays.fill(minNumbers[0], Integer.MAX_VALUE);
		Arrays.fill(minNumbers[1], Integer.MAX_VALUE);
		Arrays.fill(minFeatures, Integer.MAX_VALUE);
		
		while (!solutionList.isEmpty()) {
			List<String> curSolution = solutionList.remove();
			int[] featureList = interfaceProject.getFeatureIDs(solutionList.remove());
			solutionId++;
			
			SignatureIterator it = interfaceProject.getProjectSignatures().createIterator();
			it.addFilter(new FeatureFilter(featureList));
			it.addFilter(new ViewTagFilter(interfaceProject.getFilterViewTag()));
			ProjectStructure sig = new ProjectStructure(it);
//			ProjectStructure sig = interfaceProject.getProjectSignatures().toProjectStructure(new DefaultFilter(featureList, interfaceProject.getFilterViewTag()));
			
			SignatureGroup sigGroup = signatureMap.get(sig);
			if (sigGroup == null) {
				sigGroup = new SignatureGroup(++groupId, groupListFolder.getFolder("interface_" + converter.convert(groupId)));
				signatureMap.put(sig, sigGroup);
			}
			
			sigGroup.addSig();
			IFolder groupFolder = sigGroup.getFolder();
			
			if (!groupFolder.exists()) {
				try {
					groupFolder.create(true, true, null);
					IOConstants.writeToFile(groupFolder.getFile("statistics.txt"), sig.getStatisticsString());
				} catch (CoreException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
			}
			
			int[] x = sig.getStatisticsNumbers();
			for (int i = 0; i < x.length; i++) {
				if (minNumbers[0][i] > x[i]) {
					minNumbers[0][i] = x[i];
					solutionIds[0][i] = solutionId;
					groupIds[0][i] = sigGroup.getId();
				}
				if (minFeatures[i] > featureList.length 
						|| (minFeatures[i] == featureList.length 
							&& minNumbers[1][i] > x[i])) {
					minFeatures[i] = featureList.length;
					minNumbers[1][i] = x[i];
					solutionIds[1][i] = solutionId;
					groupIds[1][i] = sigGroup.getId();
				}
			}
			
			writeSolutionList(curSolution, groupFolder.getFile("featureList_" + converter.convert(solutionId) + IOConstants.EXTENSION_SOLUTION));
			worked();
		}
		
		StringBuilder sb2 = new StringBuilder();
		sb2.append("Min #Classes: ");
		sb2.append(minNumbers[0][0]);
		sb2.append(" (Solution ");
		sb2.append(converter.convert(solutionIds[0][0]));
		sb2.append(" in Group ");
		sb2.append(converter.convert(groupIds[0][0]));
		sb2.append(")\n");

		sb2.append("Min #Fields: ");
		sb2.append(minNumbers[0][1]);
		sb2.append(" (Solution ");
		sb2.append(converter.convert(solutionIds[0][1]));
		sb2.append(" in Group ");
		sb2.append(converter.convert(groupIds[0][1]));
		sb2.append(")\n");

		sb2.append("Min #Methods: ");
		sb2.append(minNumbers[0][2]);
		sb2.append(" (Solution ");
		sb2.append(converter.convert(solutionIds[0][2]));
		sb2.append(" in Group ");
		sb2.append(converter.convert(groupIds[0][2]));
		sb2.append(")\n");
		
		IOConstants.writeToFile(interfaceFolder.getFile("Min_Statistics.txt"), sb2.toString());
		
		SignatureGroup[] signatureArray = new SignatureGroup[signatureMap.size()];
		signatureMap.values().toArray(signatureArray);
		Arrays.sort(signatureArray);
		
		if (signatureArray.length > 0) {
			int curNumber = signatureArray[signatureArray.length - 1].size();
			int count = 0;
			final StringBuilder sb = new StringBuilder("Number of Solutions -> IDs");
			sb.append(IOConstants.LINE_SEPARATOR);
			sb.append(IOConstants.LINE_SEPARATOR);
			sb.append(curNumber);
			
			for (int i = signatureArray.length - 1; i >= 0; i--) {
				SignatureGroup sigGroup = signatureArray[i];
				if (curNumber > sigGroup.size()) {
					curNumber = sigGroup.size();
					sb.append(IOConstants.LINE_SEPARATOR);
					sb.append("\tCount : ");
					sb.append(count);
					count = 0;
					sb.append(IOConstants.LINE_SEPARATOR);
					sb.append(curNumber);
				}
				sb.append(count++ == 0 ? ':' + IOConstants.LINE_SEPARATOR + "\tIDs   : " : ", ");
				sb.append(converter.convert(sigGroup.getId()));
			}

			sb.append(IOConstants.LINE_SEPARATOR);
			sb.append("\tCount : ");
			sb.append(count);
			
			IOConstants.writeToFile(interfaceFolder.getFile("NumberOfSolutions.txt"), sb.toString());
		}
		
		MPLPlugin.getDefault().logInfo("Built Configuration Interfaces: " + signatureMap.size() + " / " + numberSolutions);
		return true;
	}
	
	private void writeSolutionList(List<String> featureList, IFile outputFile) {
		final StringBuilder solutionString = new StringBuilder();
		for (String featureName : featureList) {
			solutionString.append(featureName);
			solutionString.append(IOConstants.LINE_SEPARATOR);
		}
		IOConstants.writeToFile(outputFile, solutionString.toString());
	}
}
