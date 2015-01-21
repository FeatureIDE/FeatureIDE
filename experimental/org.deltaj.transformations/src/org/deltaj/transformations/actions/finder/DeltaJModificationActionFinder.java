package org.deltaj.transformations.actions.finder;

import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.IDeltaJAction;

/**
 * Searches through a DeltaJ program and returns all modification actions.
 * 
 * @author Oliver Richers
 */
public class DeltaJModificationActionFinder extends AbstractActionFinder {

	private final String targetName;

	public DeltaJModificationActionFinder() {

		this(null);
	}

	public DeltaJModificationActionFinder(String targetName) {

		this.targetName = targetName;
	}

	@Override
	protected boolean matches(IDeltaJAction action) {

		if (action.getActionType() == DeltaJActionType.MODIFICATION) {
			return targetName == null || action.getTargetName().equals(targetName);
		} else {
			return false;
		}
	}
}
