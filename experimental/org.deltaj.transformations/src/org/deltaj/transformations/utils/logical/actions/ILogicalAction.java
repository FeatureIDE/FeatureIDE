package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.transformations.actions.DeltaJActionType;
import org.deltaj.transformations.actions.targets.DeltaJActionTarget;
import org.deltaj.transformations.utils.logical.LogicalActionMap;

public interface ILogicalAction {

	String getFullTargetName();

	DeltaJActionTarget getTarget();

	DeltaJActionType getActionType();

	void applyWithInverse(LogicalActionMap targetActions, LogicalActionMap inverseActions);
}
