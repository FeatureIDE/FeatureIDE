package org.deltaj.transformations.actions.finder;

import org.deltaj.transformations.actions.IDeltaJAction;

/**
 * Searches through the program to find all actions affecting a given target.
 * 
 * @author Oliver Richers
 */
public class DeltaJActionByTargetFinder extends AbstractActionFinder {

	private final String targetName;

	public DeltaJActionByTargetFinder(String targetName) {

		this.targetName = targetName;
	}

	@Override
	protected boolean matches(IDeltaJAction action) {

		return action.getTargetName().equals(targetName);
	}
}
