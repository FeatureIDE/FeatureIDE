package org.deltaj.transformations.finder.product;

import java.util.Set;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.SetFactory;

public class DeltaJProductsOfProductLineFinder {

	private final ProductLine productLine;
	private final Program program;

	public DeltaJProductsOfProductLineFinder(ProductLine productLine) {

		this.program = DeltaJHierarchy.getProgram(productLine);
		this.productLine = productLine;
	}

	public Set<Product> find() {

		Set<Product> products = SetFactory.createIdentityHashSet();

		for (Product product: program.getProducts()) {
			if (product.getProductLine() == productLine) {
				products.add(product);
			}
		}

		return products;
	}
}
