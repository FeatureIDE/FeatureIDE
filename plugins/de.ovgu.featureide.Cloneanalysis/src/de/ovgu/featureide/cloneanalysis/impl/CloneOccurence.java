package de.ovgu.featureide.cloneanalysis.impl;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.cloneanalysis.results.Clone;
import de.ovgu.featureide.cloneanalysis.results.CloneAnalysisResults;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;

/**
 * Data container object that holds the data of an occurence of a code clone,
 * namely the file in which it was found and the line index at which the clone
 * begins.
 * 
 * 
 * @see {@link Clone}, {@link CloneAnalysisResults}
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public class CloneOccurence {
	/**
	 * The file in which duplicate code was detected.
	 */
	private final IPath file;
	/**
	 * The line number of the first cloned line.
	 */
	private final int startIndex;
	/**
	 * The {@link Clone}, of which this is an occurence.
	 */
	private VariantAwareClone clone;

	/**
	 * variables to split the path
	 */
	private IPath folderPath = null, featurePath = null;
	int lengthOfThePath;

	public CloneOccurence(String path, int startIndex, Clone clone) {
		this.file = new Path(path);
		this.startIndex = startIndex;
		this.clone = (VariantAwareClone) clone;
	}

	public CloneOccurence(String path, int startIndex) {
		this.file = new Path(path);
		this.startIndex = startIndex;
		// code to split the path into feature path and folder path
		split(file);
	}

	private void split(IPath file) {

		lengthOfThePath = this.getFile().segmentCount();
		folderPath = getFolderPath(lengthOfThePath);
		featurePath = this.getFile().uptoSegment(lengthOfThePath);
		String temp = featurePath.toString();
		temp = temp.substring(folderPath.toString().length(), featurePath.toString().length());
		featurePath = new Path(temp);
	}

	private IPath getFolderPath(int pathLength) {

		String featureName = this.getFile().segment(lengthOfThePath - 5);
		if (featureName.equalsIgnoreCase("features"))
			return this.getFile().uptoSegment(pathLength - 4);
		else
			return this.getFile().uptoSegment(pathLength - 5);
	}

	public IPath getFeaturePath() {
		return featurePath;
	}

	/**
	 * @return the file
	 */
	public IPath getFile() {
		return file;
	}

	/**
	 * @return the startIndex
	 */
	public int getStartIndex() {
		return startIndex;
	}

	/**
	 * @return the clone
	 */
	public VariantAwareClone getClone() {
		return clone;
	}

	/**
	 * @param clone
	 *            the clone to set
	 */
	public void setClone(VariantAwareClone clone) {
		this.clone = clone;
	}

	@Override
	public String toString() {
		// subtract places from the total length, so that it remains location
		// independent.
		lengthOfThePath = this.getFile().segmentCount();
		String featureName = this.getFile().segment(lengthOfThePath - 5);
		if (featureName.equalsIgnoreCase("features"))
			return "[" + this.getFile().segment(lengthOfThePath - 4) + "]" + this.getFile().lastSegment().toString()
					+ ":" + String.valueOf(this.getStartIndex());
		else
			return "[" + this.getFile().segment(lengthOfThePath - 5) + "]" + this.getFile().lastSegment().toString()
					+ ":" + String.valueOf(this.getStartIndex());
		// return this.getFile().lastSegment().toString() + ":" +
		// String.valueOf(this.getStartIndex());
	}
}