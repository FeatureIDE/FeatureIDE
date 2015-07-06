package de.ovgu.featureide.featurehouse.refactoring.visitors;

import java.util.List;
import java.util.Set;

import de.ovgu.featureide.featurehouse.refactoring.SearchMatch;


public interface  IASTVisitor {
	List<SearchMatch> getMatches();
	
	void startVisit();

	Set<String> getErrors();
}
