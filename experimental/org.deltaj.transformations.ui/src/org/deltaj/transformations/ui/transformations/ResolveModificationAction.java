package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.MethodModification;
import org.deltaj.transformations.resolve.DeltaJModificationActionResolver;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class ResolveModificationAction extends AbstractTransformationCommandHandler {

	public ResolveModificationAction() {

		super(
				"Resolve Modification Action",
				IconEnum.RESOLVE_MODIFY,
				"Converts method modification actions into method addition actions by extracting preceding actions and changing their application conditions.");
	}

	void transform(MethodModification action) {

		new DeltaJModificationActionResolver(action).resolve();
	}
}
