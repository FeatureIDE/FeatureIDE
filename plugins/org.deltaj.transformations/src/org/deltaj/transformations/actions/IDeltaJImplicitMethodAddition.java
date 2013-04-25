package org.deltaj.transformations.actions;

import org.deltaj.deltaj.Method;

/**
 * This is an implicit method addition action, as part of a class addition
 * action.
 * 
 * @author Oliver Richers
 */
public interface IDeltaJImplicitMethodAddition extends IDeltaJAction {

	@Override
	Method getActionStatement();
}
