package org.deltaj.transformations.facade;

import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;

public interface DeltaJExtractingDeltaActions {

	void extractDeltaAction(DeltaAction deltaAction);

	void extractMatchingActions(DeltaModule deltaModuleA, DeltaModule deltaModuleB);
}
