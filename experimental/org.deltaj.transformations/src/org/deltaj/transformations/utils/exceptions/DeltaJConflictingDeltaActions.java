package org.deltaj.transformations.utils.exceptions;

import org.deltaj.transformations.utils.logical.actions.ILogicalAction;

public class DeltaJConflictingDeltaActions extends DeltaJException {

	private final ILogicalAction actionA;
	private final ILogicalAction actionB;

	public DeltaJConflictingDeltaActions(ILogicalAction actionA, ILogicalAction actionB) {

		super("Conflicting delta actions for target '%s'.", actionA.getTarget().getFullName());

		this.actionA = actionA;
		this.actionB = actionB;
	}

	public ILogicalAction getActionA() {

		return actionA;
	}

	public ILogicalAction getActionB() {

		return actionB;
	}

}
