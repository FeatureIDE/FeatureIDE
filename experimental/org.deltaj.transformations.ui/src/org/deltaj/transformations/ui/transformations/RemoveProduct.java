package org.deltaj.transformations.ui.transformations;

import org.deltaj.deltaj.Product;
import org.deltaj.transformations.evolution.DeltaJProductRemover;
import org.deltaj.transformations.ui.menu.IconEnum;
import org.deltaj.transformations.ui.transformation.AbstractTransformationCommandHandler;

class RemoveProduct extends AbstractTransformationCommandHandler {

	public RemoveProduct() {

		super("Remove Product", IconEnum.REMOVE, "Removes a product from the product line.");
	}

	void transform(Product product) {

		new DeltaJProductRemover(product).remove();
	}
}
