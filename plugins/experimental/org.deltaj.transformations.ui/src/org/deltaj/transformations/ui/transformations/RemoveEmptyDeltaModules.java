package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.remove.module.DeltaJEmptyModulesRemover;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class RemoveEmptyDeltaModules extends AbstractTransformationCommandHandler {

	public RemoveEmptyDeltaModules() {

		super(
				"Remove Empty Delta Modules",
				IconEnum.REMOVE_DELTA,
				"Removes empty delta modules and all their references from a program.");
	}

	void transform(Program program) {

		new DeltaJEmptyModulesRemover(program).remove();
	}

	void transform(ProductLine productLine) {

		new DeltaJEmptyModulesRemover(productLine).remove();
	}

	void transform(DeltaPartition partition) {

		new DeltaJEmptyModulesRemover(partition).remove();
	}

	void transform(PartitionPart partitionPart) {

		new DeltaJEmptyModulesRemover(partitionPart).remove();
	}
}
