package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.ModuleReference;
import org.deltaj.transformations.simplify.DeltaJApplicationConditionSimplifier;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

public class SimplifyApplicationConditions extends AbstractTransformationCommandHandler {

	public SimplifyApplicationConditions() {

		super(
				"Simplify Application Conditions",
				IconEnum.CONFIGURATIONS,
				"Tries to simplify the application conditions.");
	}

	void transform(ModuleReference moduleReference) {

		new DeltaJApplicationConditionSimplifier(moduleReference).simplify();
	}
}
