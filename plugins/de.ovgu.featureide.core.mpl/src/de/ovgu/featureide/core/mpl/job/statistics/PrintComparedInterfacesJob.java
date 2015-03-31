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
package de.ovgu.featureide.core.mpl.job.statistics;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.signature.filter.ViewTagFilter;
import de.ovgu.featureide.core.mpl.util.NumberConverter;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.signature.filter.IFilter;
import de.ovgu.featureide.fm.core.io.IOConstants;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Compares different configuration interfaces.
 * 
 * @author Sebastian Krieter
 */
@SuppressWarnings("unused")
public class PrintComparedInterfacesJob extends AProjectJob<PrintComparedInterfacesJob.Arguments> {
	
	public static class Arguments extends JobArguments {
		public Arguments() {
			super(Arguments.class);
		}
	}
	
	protected PrintComparedInterfacesJob(Arguments arguments) {
		super("Compare Configuration Interfaces", arguments);
	}

	@Override
	protected boolean work() {
		InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(this.project);
		if (interfaceProject == null) {
			MPLPlugin.getDefault().logWarning(this.project.getName() + " is no Interface Project!");
			return false;
		}
		
		workMonitor.createSubTask("Calculate Solutions");
		
		final int configLimit = interfaceProject.getConfigLimit();
		
		final LinkedList<List<String>> solutionList;
		try {
			solutionList = interfaceProject.getConfiguration().getSolutions(configLimit);
		} catch (TimeoutException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		workMonitor.createSubTask("Generate Signatures");
		
		final HashSet<ProjectStructure> signatures = new HashSet<ProjectStructure>();
		
		final LinkedList<ProjectStructure> signaturesList = new LinkedList<ProjectStructure>();
		final LinkedList<Integer> groupIdList = new LinkedList<Integer>();
		
		final NumberConverter converter = new NumberConverter(solutionList.size());
		int groupId = 0;
		SignatureIterator it = interfaceProject.getProjectSignatures().iterator();
		IFilter<AbstractSignature> viewTagFilter = new ViewTagFilter(interfaceProject.getFilterViewTag());
		while (!solutionList.isEmpty()) {
			it.clearFilter();
			it.addFilter(new FeatureFilter(interfaceProject.getFeatureIDs(solutionList.remove())));
			it.addFilter(viewTagFilter);
			
			ProjectStructure sig = new ProjectStructure(it);
			if (signatures.add(sig)) {
				signaturesList.add(sig);
				groupIdList.add(++groupId);
			}
		}
		final int 
			numberSignatures = signatures.size(),
			numberCompares = (numberSignatures*(numberSignatures - 1)) >> 1;
		
		workMonitor.createSubTask("Compare Signatures");
		workMonitor.setMaxAbsoluteWork(numberCompares);
		
		final double[] compareValues = new double[numberCompares];
		int compareIndex = 0;
		
		while (!signaturesList.isEmpty()) {
			ProjectStructure sig = signaturesList.remove();
			for (ProjectStructure otherSig : signaturesList) {
//				compareValues[compareIndex++] = sig.similarityTo(otherSig);
				workMonitor.worked();
			}	
		}
		
		final StringBuilder similarityQString = new StringBuilder();
		for (int id : groupIdList) {
			similarityQString.append(converter.convert(id));
			similarityQString.append(',');
		}
		similarityQString.deleteCharAt(similarityQString.length() - 1);
		similarityQString.append(IOConstants.LINE_SEPARATOR);

		for (int i = 0; i < numberSignatures; i++) {
			for (int j = 0; j < numberSignatures; j++) {
				if (i < j) {
					similarityQString.append(compareValues[getIndex(i, j, numberSignatures)]);
				} else if (i > j) {
					similarityQString.append(compareValues[getIndex(j, i, numberSignatures)]);
				} else {
					similarityQString.append("1.0");
				}
				similarityQString.append(',');
			}
			similarityQString.deleteCharAt(similarityQString.length() - 1);
			similarityQString.append(IOConstants.LINE_SEPARATOR);
		}
		IOConstants.writeToFile(interfaceProject.getProjectReference().getFile(IOConstants.FILENAME_COMPARE_MATRIX), similarityQString.toString());
		MPLPlugin.getDefault().logInfo("Compared " + numberSignatures + " different Interfaces");
		return true;
	}

	private int getIndex(int i, int j, int max) {
		return j + (i * max) - (((i + 3) * i) >> 1) - 1;
	}
}
