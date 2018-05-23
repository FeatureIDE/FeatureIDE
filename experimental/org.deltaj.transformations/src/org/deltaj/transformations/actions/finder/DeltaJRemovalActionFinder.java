package org.deltaj.transformations.actions.finder;

import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.IDeltaJAction;

/**
 * Searches through a DeltaJ program and returns all removal actions.
 * 
 * @author Oliver Richers
 */
public class DeltaJRemovalActionFinder extends AbstractActionFinder {

	private final String targetName;

	public DeltaJRemovalActionFinder() {

		this(null);
	}

	public DeltaJRemovalActionFinder(String targetName) {

		this.targetName = targetName;
	}

	@Override
	protected boolean matches(IDeltaJAction action) {

		if (action.getActionType() == DeltaJActionType.REMOVAL) {
			return targetName == null || action.getTargetName().equals(targetName);
		} else {
			return false;
		}
	}
}
