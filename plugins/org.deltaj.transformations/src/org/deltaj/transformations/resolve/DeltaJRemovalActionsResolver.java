package org.deltaj.transformations.resolve;

import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.actions.IDeltaJAction;
import org.deltaj.transformations.actions.finder.DeltaJRemovalActionFinder;

public class DeltaJRemovalActionsResolver {

	public void resolve(ProductLine productLine) {

		for (IDeltaJAction action: new DeltaJRemovalActionFinder().find(productLine)) {
			new DeltaJRemovalActionResolver(action).resolve();
		}
	}
}
