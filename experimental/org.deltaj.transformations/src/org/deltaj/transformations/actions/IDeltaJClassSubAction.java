package org.deltaj.transformations.actions;

import org.deltaj.deltaj.DeltaSubAction;

/**
 * A class sub action adds, removes or modifies a method, or it adds or removes
 * a field.
 * 
 * @author Oliver Richers
 * 
 */
public interface IDeltaJClassSubAction extends IDeltaJAction {

	@Override
	DeltaSubAction getActionStatement();
}
