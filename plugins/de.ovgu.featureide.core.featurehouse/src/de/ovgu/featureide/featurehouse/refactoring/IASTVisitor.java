package de.ovgu.featureide.featurehouse.refactoring;

import java.util.List;


public interface  IASTVisitor {
	List<SearchMatch> getMatches();
	
	void startVisit();
}
