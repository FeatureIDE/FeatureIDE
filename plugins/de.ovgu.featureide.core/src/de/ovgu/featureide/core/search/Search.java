package de.ovgu.featureide.core.search;



public abstract class Search {
	
	protected String filter;
	protected SearchResult result;
	
	public Search(String filter, SearchResult result){
		this.filter = filter;
		this.result = result;
	}
	
	public abstract boolean performSearch();
	
}
