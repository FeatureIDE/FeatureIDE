package de.ovgu.featureide.core.search;



public abstract class Search {
	
	protected String filter;
	protected SearchResult result;
	protected String regex;
	
	public Search(String filter, SearchResult result){
		this.filter = filter;
		this.result = result;
		regex = "(.*)"+filter+"(.*)";
	}
	
	public abstract boolean performSearch();
	
}
