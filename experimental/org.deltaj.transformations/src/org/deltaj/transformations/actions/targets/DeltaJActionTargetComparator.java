package org.deltaj.transformations.actions.targets;

import java.util.Comparator;

public class DeltaJActionTargetComparator implements Comparator<DeltaJActionTarget> {

	private static DeltaJActionTargetComparator singleton = new DeltaJActionTargetComparator();

	private DeltaJActionTargetComparator() {

		// singleton
	}

	public static DeltaJActionTargetComparator get() {

		return singleton;
	}

	@Override
	public int compare(DeltaJActionTarget left, DeltaJActionTarget right) {

		// compare target types
		int cmp1 = left.getTargetType().compareTo(right.getTargetType());
		if (cmp1 != 0) {
			return cmp1;
		}

		// compare class names
		int cmp2 = left.getClassName().compareTo(right.getClassName());
		if (cmp2 != 0) {
			return cmp2;
		}

		// compare sub names
		return left.getSubName().compareTo(right.getSubName());
	}
}
