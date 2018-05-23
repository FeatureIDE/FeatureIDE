package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.transformations.resolve.DeltaJRemovalActionResolver;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class ResolveRemovalAction extends AbstractTransformationCommandHandler {

	public ResolveRemovalAction() {

		super(
				"Resolve Removal Action",
				IconEnum.RESOLVE_REMOVE,
				"Removes class, method or field removal actions by extracting preceding actions and changing their application conditions.");
	}

	void transform(ClassRemoval action) {

		new DeltaJRemovalActionResolver(action).resolve();
	}

	void transform(MethodRemoval action) {

		new DeltaJRemovalActionResolver(action).resolve();
	}

	void transform(FieldRemoval action) {

		new DeltaJRemovalActionResolver(action).resolve();
	}
}
