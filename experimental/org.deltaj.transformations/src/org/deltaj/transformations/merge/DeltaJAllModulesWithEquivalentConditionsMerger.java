package org.deltaj.transformations.merge;

import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;

public class DeltaJAllModulesWithEquivalentConditionsMerger {

	public void merge(ProductLine productLine) {

		for (PartitionPart partitionPart: productLine.getPartition().getParts()) {
			new DeltaJModulesWithEquivalentConditionsOfPartitionPartMerger(partitionPart).merge();
		}
	}
}
