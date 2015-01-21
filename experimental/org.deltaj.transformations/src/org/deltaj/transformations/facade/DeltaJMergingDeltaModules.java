package org.deltaj.transformations.facade;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;

public interface DeltaJMergingDeltaModules {

	void mergeDeltaModulesWithEquivalentConditions(DeltaModule deltaModuleA, DeltaModule deltaModuleB);

	void mergeDeltaModulesWithEquivalentConditions(PartitionPart partitionPart);

	void mergeDeltaModulesWithEquivalentConditions(ProductLine productLine);

	void mergeDeltaModulesWithEquivalentContent(DeltaModule deltaModuleA, DeltaModule deltaModuleB);

	void mergeDeltaModulesWithEquivalentContent(ProductLine productLine);

	void mergeDeltaModulesWithInverse(DeltaModule deltaModuleA, DeltaModule deltaModuleB);
}
