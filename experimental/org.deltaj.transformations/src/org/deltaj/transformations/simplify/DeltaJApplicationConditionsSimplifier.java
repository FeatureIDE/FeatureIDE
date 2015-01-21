package org.deltaj.transformations.simplify;

import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;

public class DeltaJApplicationConditionsSimplifier {

	public void simplify(ProductLine productLine) {

		for (PartitionPart partitionPart: productLine.getPartition().getParts()) {
			simplify(partitionPart);
		}
	}

	public void simplify(PartitionPart partitionPart) {

		for (ModuleReference moduleReference: partitionPart.getModuleReferences()) {
			new DeltaJApplicationConditionSimplifier(moduleReference).simplify();
		}
	}
}
