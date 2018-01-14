package de.ovgu.featureide.cloneanalysis.pmd;

import java.util.Iterator;

import net.sourceforge.pmd.cpd.Match;

public interface ICloneAnalyzerAdapter<Tool> {

	/**
	 * Initializes the Tool which is used by the Adapter.
	 */
	public abstract void initializeTool();

	/**
	 * Register the files to be analyzed with the tool.
	 */
	public abstract void registerFilesForAnalysis(Object files);

	/**
	 * Starts the analysis and may return the analysis results.
	 * 
	 * @return the analysis results, or null.
	 */
	public abstract Object startAnalysis();

	public Iterator<Match> getMatches();

}
