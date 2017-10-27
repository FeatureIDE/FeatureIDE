package de.ovgu.featureide.cloneanalysis.results;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;

public class Clone implements Comparable<Clone> {
	private int lineCount;
	private int tokenCount;
	private int fileCount;
	/**
	 * The clones code fragment.
	 */
	private String code;

	/**
	 * Value for an occurence is the Handle to an eclipse {@link IResource}
	 * interface for ease of use.
	 */
	protected Map<CloneOccurence, IFile> occurences = null;

	protected Set<IProject> relevantProjects = null;

	public Clone(Set<CloneOccurence> occurences, int lines, int tokens, int files, String code) {
		lineCount = lines;
		tokenCount = tokens;
		fileCount = files;
		this.code = code;
		populateOccurences(occurences);
	}

	/**
	 * Adds Occurences from the given {@link Set} into the Clones occurences
	 * {@link Map},
	 * 
	 * 
	 * @param occurenceSet
	 */
	private void populateOccurences(Set<CloneOccurence> occurenceSet) {
		occurences = new HashMap<CloneOccurence, IFile>();
		for (CloneOccurence occurence : occurenceSet) {
			final IFile file = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(occurence.getFile());
			final IProject project = file.getProject();

			assert project.exists() : "clone found in a file not associated to any existing project.";

			if (relevantProjects == null)
				relevantProjects = new HashSet<IProject>();

			if (!relevantProjects.contains(project))
				relevantProjects.add(project);

			occurences.put(occurence, file);
		}
	}

	@Override
	public int compareTo(Clone other) {
		if (other == null)
			return 1;
		if (getNumberOfFiles() != other.getNumberOfFiles())
			return getNumberOfFiles() - other.getNumberOfFiles();
		else
			return getLineCount() - other.getLineCount();
	}

	/**
	 * @return the occurences
	 */
	public Set<CloneOccurence> getOccurences() {
		return occurences.keySet();
	}

	/**
	 * @return the length of the cloned code snippet in lines.
	 */
	public int getLineCount() {
		return lineCount;
	}

	/**
	 * @return the tokenCount
	 */
	public int getTokenCount() {
		return tokenCount;
	}

	/**
	 * @return the fileCount
	 */
	public int getNumberOfFiles() {
		return fileCount;
	}

	/**
	 * Convenience function that returns the {@link IPath} of all Files that
	 * contain an occurence of the clone in a {@link List}. Each {@link IPath}
	 * is only listed once, even if its file contains multiple occurences.
	 * 
	 * @return
	 */
	public List<IPath> getDistinctFiles() {
		Set<IPath> files = new HashSet<IPath>();
		if (occurences != null)
			for (CloneOccurence snippet : occurences.keySet())
				files.add(snippet.getFile());
		return new ArrayList<IPath>(files);
	}

	/**
	 * @return the code
	 */
	public String getCode() {
		return code;
	}

	/**
	 * @return the relevantProjects
	 */
	public Set<IProject> getRelevantProjects() {
		return relevantProjects;
	}
}
