package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.transformations.evolution.DeltaJModuleRemover;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class RemoveDeltaModule extends AbstractTransformationCommandHandler {

	public RemoveDeltaModule() {

		super(
				"Remove Delta Module",
				IconEnum.REMOVE_DELTA,
				"Removes a delta module and all its references from a program.");
	}

	void transform(DeltaModule deltaModule) {

		new DeltaJModuleRemover(deltaModule).remove();
	}
}
