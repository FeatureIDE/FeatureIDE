package org.deltaj.transformations.exceptions;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.Product;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJModuleNotUsedByProductException extends DeltaJException {

	private final Product product;
	private final DeltaModule deltaModule;

	public DeltaJModuleNotUsedByProductException(Product product, DeltaModule deltaModule) {

		super("The delta module '%s' is not used by the product '%s'.", deltaModule.getName(), product.getName());

		this.product = product;
		this.deltaModule = deltaModule;
	}

	public Product getProduct() {

		return product;
	}

	public DeltaModule getDeltaModule() {

		return deltaModule;
	}
}
