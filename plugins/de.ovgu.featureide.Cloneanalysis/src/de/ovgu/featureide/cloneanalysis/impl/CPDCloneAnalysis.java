package de.ovgu.featureide.cloneanalysis.impl;

import java.util.Iterator;

import net.sourceforge.pmd.cpd.CPD;
import net.sourceforge.pmd.cpd.Match;
import de.ovgu.featureide.cloneanalysis.pmd.CPDAdapter;
import de.ovgu.featureide.cloneanalysis.pmd.ICloneAnalyzerAdapter;

public class CPDCloneAnalysis {
	private ICloneAnalyzerAdapter<CPD> cpdAdapter;

	public CPDCloneAnalysis() {
		cpdAdapter = new CPDAdapter();
	}

	public CPDCloneAnalysis(String filteredName) {
		cpdAdapter = new CPDAdapter(filteredName);
	}

	public Iterator<Match> analyze(Object selection) {
		// System.out.println("Starting CC analysis..");

		cpdAdapter.initializeTool();
		cpdAdapter.registerFilesForAnalysis(selection);
		cpdAdapter.startAnalysis();

		// System.out.println("CC analysis done!");

		return cpdAdapter.getMatches();
	}

	/**
	 * @return the cpdAdapter
	 */
	public ICloneAnalyzerAdapter<CPD> getCpdAdapter() {
		return cpdAdapter;
	}

}
