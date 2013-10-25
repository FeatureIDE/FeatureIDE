package de.ovgu.featureide.core.mpl.job;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.core.mpl.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.mpl.signature.ProjectStructure;
import de.ovgu.featureide.core.mpl.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.mpl.signature.filter.ISignatureFilter;
import de.ovgu.featureide.core.mpl.signature.filter.ViewTagFilter;
import de.ovgu.featureide.core.mpl.util.NumberConverter;

public class CompareConfigInterfaces extends AMonitorJob {
	
	public CompareConfigInterfaces() {
		super("Compare Configuration Interfaces");
	}

	@Override
	protected boolean work() {
		monitor.subTask("Calculate Solutions");
		
		final int configLimit = interfaceProject.getConfigLimit();
		
		final LinkedList<List<String>> solutionList;
		try {
			solutionList = interfaceProject.getConfiguration().getSolutions(configLimit);
		} catch (TimeoutException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}
		
		monitor.subTask("Generate Signatures");
		
		final HashSet<ProjectStructure> signatures = new HashSet<ProjectStructure>();
		
		final LinkedList<ProjectStructure> signaturesList = new LinkedList<ProjectStructure>();
		final LinkedList<Integer> groupIdList = new LinkedList<Integer>();
		
		final NumberConverter converter = new NumberConverter(solutionList.size());
		int groupId = 0;
		SignatureIterator it = interfaceProject.getProjectSignatures().createIterator();
		ISignatureFilter viewTagFilter = new ViewTagFilter(interfaceProject.getFilterViewTag());
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
		
		monitor.subTask("Compare Signatures");
		setMaxAbsoluteWork(numberCompares);
		
		final double[] compareValues = new double[numberCompares];
		int compareIndex = 0;
		
		while (!signaturesList.isEmpty()) {
			ProjectStructure sig = signaturesList.remove();
			for (ProjectStructure otherSig : signaturesList) {
				compareValues[compareIndex++] = sig.similarityTo(otherSig);
				worked();
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
