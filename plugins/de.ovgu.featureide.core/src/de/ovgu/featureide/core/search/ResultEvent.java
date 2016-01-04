package de.ovgu.featureide.core.search;

import org.eclipse.search.ui.SearchResultEvent;

@SuppressWarnings("serial")
public class ResultEvent extends SearchResultEvent {

	private final Result result;
	
	protected ResultEvent(SearchResult searchResult, Result result) {
		super(searchResult);
		this.result = result;
	}
	
	public Result getResult(){
		return result;
	}

}
