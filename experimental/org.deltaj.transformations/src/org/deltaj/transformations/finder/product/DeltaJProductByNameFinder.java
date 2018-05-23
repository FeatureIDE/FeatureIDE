package org.deltaj.transformations.finder.product;

import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.Program;

/**
 * Searches through a {@link Program} to find a product with the specified name.
 * 
 * @author Oliver Richers
 */
public class DeltaJProductByNameFinder {

	private final Program program;
	private final String productName;

	/**
	 * Constructs this finder.
	 * 
	 * @param program
	 *            the program to search in
	 * @param productName
	 *            the name of the product
	 */
	public DeltaJProductByNameFinder(Program program, String productName) {

		this.program = program;
		this.productName = productName;
	}

	/**
	 * Returns the product with the given name or null if no such product
	 * exists.
	 */
	public Product find() {

		for (Product product: program.getProducts()) {
			if (product.getName().equals(productName)) {
				return product;
			}
		}

		return null;
	}

	/**
	 * Returns the product with the given name.
	 * 
	 * @throws IllegalArgumentException
	 *             if no matching product can be found
	 */
	public Product findOrThrow() {

		Product product = find();

		if (product == null) {
			throw new IllegalArgumentException(String.format("The product with the name '%s' could not be found.", productName));
		}

		return product;
	}
}
