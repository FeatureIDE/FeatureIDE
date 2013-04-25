package org.deltaj.transformations.actions;

/**
 * Three different types of targets can be affected by a delta action: classes,
 * methods and fields.
 * 
 * @author Oliver Richers
 */
public enum DeltaJActionTargetType {

	CLASS,
	METHOD,
	FIELD
}
