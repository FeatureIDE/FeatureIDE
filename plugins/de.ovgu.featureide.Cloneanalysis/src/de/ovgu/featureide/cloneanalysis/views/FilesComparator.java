package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;

public class FilesComparator extends ViewerComparator {

	boolean sortDescending;

	public FilesComparator(boolean sortDescending) {
		this.sortDescending = sortDescending;
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		int f1 = 0, f2 = 0, result = 0;
		if (e1 instanceof Clone)
			f1 = ((Clone) e1).getNumberOfFiles();
		else if (e1 instanceof CloneOccurence)
			f1 = ((CloneOccurence) e1).getClone().getNumberOfFiles();
		if (e2 instanceof Clone)
			f2 = ((Clone) e2).getNumberOfFiles();
		else if (e2 instanceof CloneOccurence)
			f2 = ((CloneOccurence) e2).getClone().getNumberOfFiles();

		if (sortDescending == true) {
			result = f2 - f1;
		} else {
			result = f1 - f2;
		}

		return result;
	}
}
