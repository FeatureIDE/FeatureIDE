package org.deltaj.transformations.actions;

import org.deltaj.deltaj.DeltaAction;

/**
 * A class action adds, removes or modifies a class.
 * 
 * @author Oliver Richers
 */
public interface IDeltaJClassAction extends IDeltaJAction {

	@Override
	DeltaAction getActionStatement();
}
