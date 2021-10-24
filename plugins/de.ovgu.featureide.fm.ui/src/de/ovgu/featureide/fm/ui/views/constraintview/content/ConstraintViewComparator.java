package de.ovgu.featureide.fm.ui.views.constraintview.content;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;

import de.ovgu.featureide.fm.core.base.IConstraint;

/**
 * This class handles the sorting of the Columns in the ConstraintView.
 *
 * Can sort either by the ConstraintColumn or the DescriptionColumn of the ConstraintView. Uses the String value of the ConstraintColumn to sort alphabetically.
 * Uses the String value of the DescriptionColumn to sort alphabetically. Empty descriptions will be sorted below non-empty descriptions.
 *
 * Upon sorting a column again, the sorting direction is reverted (ascending to descending and vice versa).
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintViewComparator extends ViewerComparator {

	private int column = CONSTRAINT_COLUMN;
	private int direction = ASCENDING;

	public static final int CONSTRAINT_COLUMN = 0;
	public static final int DESCRIPTION_COLUMN = 1;
	public static final int TAG_COLUMN = 2;
	public static final int ASCENDING = 0;
	public static final int DESCENDING = 1;

	public int getDirection() {
		return direction == DESCENDING ? SWT.DOWN : SWT.UP;
	}

	public void setColumn(int newColumn) {
		if (newColumn == column) {
			direction = 1 - direction;
		} else {
			column = newColumn;
			direction = ASCENDING;
		}
	}

	public void setDirection(int direction) {
		this.direction = direction;
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		final IConstraint constraint1 = (IConstraint) e1;
		final IConstraint constraint2 = (IConstraint) e2;

		int diff = 0;
		switch (column) {
		case CONSTRAINT_COLUMN:
			diff = compareConstraintName(constraint1, constraint2);
			break;
		case DESCRIPTION_COLUMN:
			diff = compareDescription(constraint1, constraint2);
			break;
		case TAG_COLUMN:
			diff = compareTags(constraint1, constraint2);
			break;
		}

		if (direction == DESCENDING) {
			diff = -diff;
		}

		return diff;
	}

	public int compareConstraintName(IConstraint constraint1, IConstraint constraint2) {
		return constraint1.getDisplayName().compareTo(constraint2.getDisplayName());
	}

	public int compareDescription(IConstraint constraint1, IConstraint constraint2) {
		// empty descriptions should appear below non-empty descriptions
		if ("".equals(constraint2.getDescription())) {
			return -1;
		} else if ("".equals(constraint1.getDescription())) {
			return 1;
		}
		return constraint1.getDescription().compareTo(constraint2.getDescription());
	}

	private int compareTags(IConstraint constraint1, IConstraint constraint2) {
		String constraint1FirstTag = "";
		if (!constraint1.getTags().isEmpty()) {
			constraint1FirstTag = constraint1.getTags().iterator().next();
		}
		String constraint2FirstTag = "";
		if (!constraint2.getTags().isEmpty()) {
			constraint2FirstTag = constraint2.getTags().iterator().next();
		}
		int diff = constraint1FirstTag.compareTo(constraint2FirstTag);
		if (diff == 0) {
			diff = Math.abs(constraint1.getTags().size() - constraint2.getTags().size());
		}
		return diff;
	}
}
