package org.deltaj.transformations.actions;

import org.deltaj.deltaj.Field;

/**
 * This is an implicit field addition action, as part of a class addition
 * action.
 * 
 * @author Oliver Richers
 */
public interface IDeltaJImplicitFieldAddition extends IDeltaJAction {

	@Override
	Field getActionStatement();
}
