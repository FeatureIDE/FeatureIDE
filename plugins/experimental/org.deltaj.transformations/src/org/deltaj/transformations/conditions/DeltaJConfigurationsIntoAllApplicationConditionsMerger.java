package org.deltaj.transformations.conditions;

import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;

public class DeltaJConfigurationsIntoAllApplicationConditionsMerger {

	public void merge(ProductLine productLine) {

		for (PartitionPart partitionPart: productLine.getPartition().getParts()) {
			for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {
				new DeltaJConfigurationsIntoApplicationConditionsMerger(moduleReference).merge();
			}
		}
	}
}
