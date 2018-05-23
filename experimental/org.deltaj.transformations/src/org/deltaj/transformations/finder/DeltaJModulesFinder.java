package org.deltaj.transformations.finder;

import java.util.Set;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.SetFactory;

public class DeltaJModulesFinder {

	public Set<DeltaModule> find(ProductLine productLine) {

		Set<DeltaModule> deltaModules = SetFactory.createIdentityHashSet();

		for (PartitionPart partitionPart: productLine.getPartition().getParts()) {
			for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {
				deltaModules.add(moduleReference.getDeltaModule());
			}
		}

		return deltaModules;
	}
}
