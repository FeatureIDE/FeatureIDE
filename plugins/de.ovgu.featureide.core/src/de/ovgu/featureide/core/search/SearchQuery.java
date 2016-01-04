package de.ovgu.featureide.core.search;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.search.ui.ISearchQuery;
import org.eclipse.search.ui.ISearchResult;

public class SearchQuery implements ISearchQuery {

	@SuppressWarnings("unused")
	private final int CHECKED; 
	private boolean checked[];
	private String filter;
	private SearchResult searchResult;
	
	
	public SearchQuery(String txt, boolean[] checked, int CHECKED){
		this.CHECKED = CHECKED;
		this.checked = checked;
		this.filter = txt;	
		this.searchResult = new SearchResult(this);
	}
	
	/**array definitions (=where to search)
	 * 0...Outline
	 * 1...Configuration Editor
	 * 2...File System
	 * 3...Feature Model
	 * 4...Files
	 * 5...Collaboration Diagram
	 */
	public IStatus run(IProgressMonitor monitor) throws OperationCanceledException{
		//get workspace URI
		File root = ResourcesPlugin.getWorkspace().getRoot().getLocation().toFile();
		//get workspace projects
		IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
		
		if (checked[0] || checked[1] || checked[3] || checked[4] || checked[5]){
			//perform FeatureSearch
			FeatureSearch featureSearch = new FeatureSearch(filter,projects,searchResult);
			featureSearch.performSearch();
		}
		if (checked[2]){
			//perform FileSearch
			FileSystemSearch fileSearch = new FileSystemSearch(filter, root, searchResult);
			fileSearch.performSearch();
			
		}
		return Status.OK_STATUS;
	}

	@Override
	public String getLabel() {
		return "Feature Search";
	}

	@Override
	public boolean canRerun() {
		return true;
	}

	@Override
	public boolean canRunInBackground() {
		return false;
	}

	@Override
	public ISearchResult getSearchResult() {
		return searchResult;
	}

	
}
