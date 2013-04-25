package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.transformations.facade.DeltaJTransformationsFacade;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class ExtractMatchingActions extends AbstractTransformationCommandHandler {

	public ExtractMatchingActions() {

		super(
				"Extract Matching Actions",
				IconEnum.CUT,
				"Extract all delta actions from the module with the same target.");
	}

	void transform(DeltaModule deltaModuleA, DeltaModule deltaModuleB) {

		DeltaJTransformationsFacade.INSTANCE.extractMatchingActions(deltaModuleA, deltaModuleB);
	}
}
