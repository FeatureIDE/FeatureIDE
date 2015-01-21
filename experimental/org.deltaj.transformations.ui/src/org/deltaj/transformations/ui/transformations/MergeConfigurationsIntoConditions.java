package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.ModuleReference;
import org.deltaj.transformations.conditions.DeltaJConfigurationsIntoApplicationConditionsMerger;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class MergeConfigurationsIntoConditions extends AbstractTransformationCommandHandler {

	public MergeConfigurationsIntoConditions() {

		super("Merge Feature Configurations Into Application Conditions", IconEnum.CONFIGURATIONS, "Merges the feature configurations into the application conditions.");
	}

	void transform(ModuleReference moduleReference) {

		new DeltaJConfigurationsIntoApplicationConditionsMerger(moduleReference).merge();
	}
}
