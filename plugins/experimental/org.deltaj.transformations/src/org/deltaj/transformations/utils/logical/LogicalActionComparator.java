package org.deltaj.transformations.utils.logical;

import java.util.Comparator;
import org.deltaj.transformations.utils.DeltaJUnexpectedEnumValue;
import org.deltaj.transformations.utils.logical.actions.ILogicalAction;

public class LogicalActionComparator implements Comparator<ILogicalAction> {

	@Override
	public int compare(ILogicalAction left, ILogicalAction right) {

		int cmp1 = compareTargetType(left, right);
		if (cmp1 != 0) {
			return cmp1;
		}

		int cmp2 = compareActionType(left, right);
		if (cmp2 != 0) {
			return cmp2;
		}

		return left.getTarget().compareTo(right.getTarget());
	}

	private int compareActionType(ILogicalAction left, ILogicalAction right) {

		return getActionTypeValue(left) - getActionTypeValue(right);
	}

	private int getActionTypeValue(ILogicalAction logicalAction) {

		switch (logicalAction.getActionType()) {
		case ADDITION:
			return 0;
		case MODIFICATION:
			return 1;
		case REMOVAL:
			return 2;
		}
		throw new DeltaJUnexpectedEnumValue();
	}

	private int compareTargetType(ILogicalAction left, ILogicalAction right) {

		return getTargetTypeValue(left) - getTargetTypeValue(right);
	}

	private int getTargetTypeValue(ILogicalAction logicalAction) {

		switch (logicalAction.getTarget().getTargetType()) {
		case CLASS:
			return 0;
		case FIELD:
			return 1;
		case METHOD:
			return 2;
		}
		throw new DeltaJUnexpectedEnumValue();
	}
}
