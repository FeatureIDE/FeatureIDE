package org.deltaj.transformations.evolution;

import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListUtils;

public class DeltaJProductRemover {

	private final Product product;

	public DeltaJProductRemover(Product product) {

		this.product = product;
	}

	public void remove() {

		Program program = DeltaJHierarchy.getProgram(product);

		ListUtils.removeElementByIdentity(program.getProducts(), product);
	}
}
