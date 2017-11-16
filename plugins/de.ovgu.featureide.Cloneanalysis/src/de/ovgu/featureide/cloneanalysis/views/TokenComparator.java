package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;

public class TokenComparator extends ViewerComparator {

	boolean sortDescending;

	public TokenComparator(boolean sortDescending) {
		this.sortDescending = sortDescending;
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		int t1 = 0, t2 = 0, result = 0;
		if (e1 instanceof Clone)
			t1 = ((Clone) e1).getTokenCount();
		else if (e1 instanceof CloneOccurence)
			t1 = ((CloneOccurence) e1).getClone().getTokenCount();
		if (e2 instanceof Clone)
			t2 = ((Clone) e2).getTokenCount();
		else if (e2 instanceof CloneOccurence)
			t2 = ((CloneOccurence) e2).getClone().getTokenCount();

		if (sortDescending == true) {
			result = t2 - t1;
		} else {
			result = t1 - t2;
		}

		return result;
	}
}
