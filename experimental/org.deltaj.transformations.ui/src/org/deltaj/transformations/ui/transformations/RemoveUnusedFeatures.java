package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.Features;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.cleanup.features.DeltaJAllUnusedFeaturesRemover;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class RemoveUnusedFeatures extends AbstractTransformationCommandHandler {

	public RemoveUnusedFeatures() {

		super("Remove Unused Features", IconEnum.REMOVE_FEATURE, "Removes unused features.");
	}

	void transform(Program program) {

		new DeltaJAllUnusedFeaturesRemover().remove(program);
	}

	void transform(ProductLine productLine) {

		new DeltaJAllUnusedFeaturesRemover().remove(productLine);
	}

	void transform(Features features) {

		new DeltaJAllUnusedFeaturesRemover().remove(features);
	}
}
