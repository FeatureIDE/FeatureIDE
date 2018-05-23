package org.deltaj.transformations.finder.product.line;

import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.finder.utils.AbstractFinder;

public class DeltaJProductLineFinder extends AbstractFinder<ProductLine> {

	private final Program program;
	private final String productLineName;

	public DeltaJProductLineFinder(Program program, String productLineName) {

		this.program = program;
		this.productLineName = productLineName;
	}

	@Override
	public ProductLine find() {

		for (ProductLine productLine: program.getProductLines()) {
			if (productLine.getName().equals(productLineName)) {
				return productLine;
			}
		}

		return null;
	}
}
