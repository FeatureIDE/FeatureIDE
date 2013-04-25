package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.facade.DeltaJTransformationsFacade;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class MergeModulesWithEquivalenConditions extends AbstractTransformationCommandHandler {

	public MergeModulesWithEquivalenConditions() {

		super(
				"Merge Modules with Equivalent Conditions",
				IconEnum.MERGE,
				"Merges delta modules with equal application conditions.");
	}

	void transform(PartitionPart partitionPart) {

		DeltaJTransformationsFacade.INSTANCE.mergeDeltaModulesWithEquivalentConditions(partitionPart);
	}

	void transform(ProductLine productLine) {

		DeltaJTransformationsFacade.INSTANCE.mergeDeltaModulesWithEquivalentConditions(productLine);
	}
}
