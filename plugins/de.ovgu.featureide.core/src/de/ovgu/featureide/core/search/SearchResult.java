package de.ovgu.featureide.core.search;

import java.util.Collection;
import java.util.HashSet;

import org.eclipse.core.runtime.ListenerList;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.search.ui.ISearchQuery;
import org.eclipse.search.ui.ISearchResult;
import org.eclipse.search.ui.ISearchResultListener;

public class SearchResult implements ISearchResult {
	
	private final SearchQuery query;
	private final ListenerList listeners = new ListenerList();
	private final Collection<Result> result = new HashSet<Result>();
	
	public SearchResult(SearchQuery searchQuery) {
		query = searchQuery;
	}

	@Override
	public void addListener(ISearchResultListener l) {
		listeners.add(l);

	}

	@Override
	public void removeListener(ISearchResultListener l) {
		listeners.remove(l);
	}

	private void notifyListener(Result r){
		ResultEvent resultEvent = new ResultEvent(this, r);
		for (Object listener : listeners.getListeners())
			((ISearchResultListener) listener).searchResultChanged(resultEvent);
	}
	
	@Override
	public String getLabel() {
		return result.size() + " matches found.";
	}

	@Override
	public String getTooltip() {
		return "Matches found";
	}

	@Override
	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	@Override
	public ISearchQuery getQuery() {
		return query;
	}

	public void addResult(Result r) {
		result.add(r);
		notifyListener(r);
	}

}
