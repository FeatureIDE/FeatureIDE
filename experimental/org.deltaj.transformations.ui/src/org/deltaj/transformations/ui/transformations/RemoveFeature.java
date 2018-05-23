package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.Feature;
import org.deltaj.transformations.evolution.DeltaJFeatureRemover;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class RemoveFeature extends AbstractTransformationCommandHandler {

	public RemoveFeature() {

		super("Remove Feature", IconEnum.REMOVE_FEATURE, "Removes a feature from the product line.");
	}

	void transform(Feature feature) {

		new DeltaJFeatureRemover(feature).remove();
	}
}
