package org.deltaj.transformations.resolve;

import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.finder.DeltaJMethodModificationActionFinder;

public class DeltaJModificationActionsResolver {

	public void resolve(ProductLine productLine) {

		for (IDeltaJAction action: new DeltaJMethodModificationActionFinder().find(productLine)) {
			new DeltaJModificationActionResolver(action).resolve();
		}
	}
}
