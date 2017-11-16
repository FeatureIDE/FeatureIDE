package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;

final class SizeComparator extends ViewerComparator {

	boolean sortDescending = true;

	public SizeComparator(boolean sortDescending) {
		this.sortDescending = sortDescending;
	}

	public SizeComparator() {

	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		int s1 = 0, s2 = 0, result = 0;
		if (e1 instanceof Clone)
			s1 = ((Clone) e1).getLineCount() * ((Clone) e1).getOccurences().size();
		else if (e1 instanceof CloneOccurence)
			s1 = ((CloneOccurence) e1).getClone().getLineCount();
		if (e2 instanceof Clone)
			s2 = ((Clone) e2).getLineCount() * ((Clone) e2).getOccurences().size();
		else if (e2 instanceof CloneOccurence)
			s2 = ((CloneOccurence) e2).getClone().getLineCount();

		if (sortDescending == true) {
			result = s2 - s1;
		} else {
			result = s1 - s2;
		}

		return result;
	}
}