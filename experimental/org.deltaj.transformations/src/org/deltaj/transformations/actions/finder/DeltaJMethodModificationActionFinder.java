package org.deltaj.transformations.actions.finder;

import org.deltaj.transformations.actions.DeltaJActionTargetType;
import org.deltaj.transformations.actions.IDeltaJAction;

/**
 * Searches through a DeltaJ program and returns all modification actions.
 * 
 * @author Oliver Richers
 */
public class DeltaJMethodModificationActionFinder extends DeltaJModificationActionFinder {

	public DeltaJMethodModificationActionFinder() {

		super(null);
	}

	public DeltaJMethodModificationActionFinder(String targetName) {

		super(targetName);
	}

	@Override
	protected boolean matches(IDeltaJAction action) {

		return super.matches(action) && action.getTargetType() == DeltaJActionTargetType.METHOD;
	}
}
