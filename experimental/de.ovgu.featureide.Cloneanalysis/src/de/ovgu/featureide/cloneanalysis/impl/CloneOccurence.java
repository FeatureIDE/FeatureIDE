package de.ovgu.featureide.cloneanalysis.impl;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.cloneanalysis.results.Clone;
import de.ovgu.featureide.cloneanalysis.results.CloneAnalysisResults;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;

/**
 * Data container object that holds the data of an occurence of a code clone,
 * namely the file in which it was found and the line index at which the clone begins.
 * 
 * 
 * @see {@link Clone}, {@link CloneAnalysisResults}
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public class CloneOccurence
{
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

	public CloneOccurence(String path, int startIndex, Clone clone)
	{
		this.file = new Path(path);
		this.startIndex = startIndex;
		this.clone =(VariantAwareClone) clone;
	}
	
	public CloneOccurence(String path, int startIndex)
	{
		this.file = new Path(path);
		this.startIndex = startIndex;
	}
	
	/**
	 * @return the file
	 */
	public IPath getFile()
	{
		return file;
	}

	/**
	 * @return the startIndex
	 */
	public int getStartIndex()
	{
		return startIndex;
	}

	/**
	 * @return the clone
	 */
	public VariantAwareClone getClone()
	{
		return clone;
	}

	/**
	 * @param clone the clone to set
	 */
	public void setClone(VariantAwareClone clone)
	{
		this.clone = clone;
	}
	
	@Override
	public String toString()
	{
		return this.getFile().lastSegment().toString() + ":" + String.valueOf(this.getStartIndex());
	}
}