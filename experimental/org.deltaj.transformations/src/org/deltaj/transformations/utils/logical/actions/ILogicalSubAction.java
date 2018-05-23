package org.deltaj.transformations.utils.logical.actions;

import org.deltaj.deltaj.ClassModification;

public interface ILogicalSubAction extends ILogicalAction {

	void addTo(ClassModification classModification);
}
