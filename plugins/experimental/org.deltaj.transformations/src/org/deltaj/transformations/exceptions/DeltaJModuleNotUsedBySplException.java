package org.deltaj.transformations.exceptions;

import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class DeltaJModuleNotUsedBySplException extends DeltaJException {

	private final ProductLine splSpecification;
	private final DeltaModule deltaModule;

	public DeltaJModuleNotUsedBySplException(ProductLine splSpecification, DeltaModule deltaModule) {

		super("The delta module '%s' is not used by the spl '%s'.", deltaModule.getName(), splSpecification.getName());

		this.splSpecification = splSpecification;
		this.deltaModule = deltaModule;
	}

	public ProductLine getSplSpecification() {

		return splSpecification;
	}

	public DeltaModule getDeltaModule() {

		return deltaModule;
	}
}
