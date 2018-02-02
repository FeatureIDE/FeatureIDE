package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;

final class LinesComparator extends ViewerComparator {
	boolean sortDescending;

	public LinesComparator(boolean sortDescending) {
		this.sortDescending = sortDescending;
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		int l1 = 0, l2 = 0, result = 0;
		if (e1 instanceof Clone)
			l1 = ((Clone) e1).getLineCount();
		else if (e1 instanceof CloneOccurence)
			l1 = ((CloneOccurence) e1).getClone().getLineCount();
		if (e2 instanceof Clone)
			l2 = ((Clone) e2).getLineCount();
		else if (e2 instanceof CloneOccurence)
			l2 = ((CloneOccurence) e2).getClone().getLineCount();

		if (sortDescending == true) {
			result = l2 - l1;
		} else {
			result = l1 - l2;
		}

		return result;
	}
}