package br.ufal.ic.colligens.controllers.semanticbugs;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;
import org.eclipse.swt.SWT;

import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.util.Log;

class ViewSorter extends ViewerSorter {

	private int propertyIndex;
	private static final int DESCENDING = 1;
	private int direction = DESCENDING;

	public ViewSorter() {
		propertyIndex = 0;
		direction = DESCENDING;
	}

	public int getDirection() {
		return direction == 1 ? SWT.DOWN : SWT.UP;
	}

	public void setColumn(int column) {
		if (column == propertyIndex) {
			// Same column as last sort; toggle the direction
			direction = 1 - direction;
		} else {
			// New column; do an ascending sort
			propertyIndex = column;
			direction = DESCENDING;
		}
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		int rc = 0;

		switch (propertyIndex) {
		case 0:
			if ((e1 instanceof FileProxy) && (e2 instanceof FileProxy)) {
				rc = ((FileProxy) e1).getFileName().compareTo(((FileProxy) e2).getFileName());
			}
			if ((e1 instanceof Log) && (e2 instanceof Log)) {
				rc = ((Log) e1).getMessage().compareTo(((Log) e2).getMessage());
			}
			break;
		case 1:
			if ((e1 instanceof Log) && (e2 instanceof Log)) {
				rc = ((Log) e1).getFileName().compareTo(((Log) e2).getFileName());
			}
			break;
		case 2:
			if ((e1 instanceof Log) && (e2 instanceof Log)) {
				rc = ((Log) e1).getPath().compareTo(((Log) e2).getPath());
			}
			break;
		case 3:
			if ((e1 instanceof Log) && (e2 instanceof Log)) {
				rc = ((Log) e1).getFeature().compareTo(((Log) e2).getFeature());
			}
		default:
			rc = 0;
		}

		// If descending order, flip the direction
		if (direction == DESCENDING) {
			rc = -rc;
		}
		return rc;
	}
}
