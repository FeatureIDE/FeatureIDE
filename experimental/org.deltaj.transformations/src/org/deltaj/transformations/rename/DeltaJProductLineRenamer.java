package org.deltaj.transformations.rename;

import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ProductLine;

public class DeltaJProductLineRenamer {

	private final ProductLine productLine;
	private final String newName;

	public DeltaJProductLineRenamer(ProductLine productLine, String newName) {

		this.productLine = productLine;
		this.newName = newName;
	}

	public void rename() {

		productLine.setName(newName);

		Program program = (Program) productLine.eContainer();
		for (Product product: program.getProducts()) {
			if (product.getProductLine() == productLine) {
				product.setProductLine(null);
				product.setProductLine(productLine);
			}
		}
	}
}
