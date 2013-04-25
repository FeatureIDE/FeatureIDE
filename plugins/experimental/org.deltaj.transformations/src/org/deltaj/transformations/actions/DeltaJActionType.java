package org.deltaj.transformations.actions;

/**
 * There a three kinds of effects a delta action can have. It can add, remove or
 * modify a target entity.
 * 
 * @author Oliver Richers
 */
public enum DeltaJActionType {

	ADDITION,
	REMOVAL,
	MODIFICATION
}
