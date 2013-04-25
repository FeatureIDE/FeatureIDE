package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.extract.DeltaJActionExtractor;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class ExtractDeltaAction extends AbstractTransformationCommandHandler {

	public ExtractDeltaAction() {

		super("Extract Delta Action", IconEnum.CUT, "Extracts a delta action into a separate delta module.");
	}

	void transform(DeltaAction action) {

		new DeltaJActionExtractor(action).extract();
	}

	void transform(DeltaSubAction action) {

		new DeltaJActionExtractor(action).extract();
	}
}
