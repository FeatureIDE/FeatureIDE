package org.deltaj.transformations.rename;

import org.deltaj.deltaj.Product;

public class DeltaJProductRenamer {

	private final Product product;
	private final String newName;

	public DeltaJProductRenamer(Product product, String newName) {

		this.product = product;
		this.newName = newName;
	}

	public void rename() {

		product.setName(newName);
	}
}
