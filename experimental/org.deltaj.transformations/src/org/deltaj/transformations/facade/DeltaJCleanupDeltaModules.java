package org.deltaj.transformations.facade;

import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.deltaj.PartitionPart;

public interface DeltaJCleanupDeltaModules {

	void mergeCompatiblePartitionParts(PartitionPart partitionPartA, PartitionPart partitionPartB);

	void removeDeadDeltaAction(DeltaAction deltaAction);

	void removeDeadDeltaAction(DeltaSubAction deltaSubAction);

	void removeDeadDeltaModule(DeltaModule deltaModule);

	void removeEmptyDeltaModule(DeltaModule deltaModule);
}
