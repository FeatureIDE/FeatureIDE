package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.DeltaAction;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.DeltaSubAction;
import org.deltaj.transformations.actions.DeltaJActionFactory;
import org.deltaj.transformations.evolution.DeltaJActionRemover;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

public class RemoveDeltaAction extends AbstractTransformationCommandHandler {

	public RemoveDeltaAction() {

		super("Remove Delta Action", IconEnum.REMOVE_DELTA, "Removes a delta action from a delta module.");
	}

	void transform(DeltaAction action) {

		new DeltaJActionRemover(action).remove();
	}

	void transform(DeltaSubAction action) {

		new DeltaJActionRemover(action).remove();
	}

	void transform(Method method) {

		new DeltaJActionRemover(DeltaJActionFactory.get(method)).remove();
	}

	void transform(Field field) {

		new DeltaJActionRemover(DeltaJActionFactory.get(field)).remove();
	}
}
