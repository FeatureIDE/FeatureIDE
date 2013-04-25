package org.deltaj.transformations.finder.product;

import java.util.List;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListFactory;
import org.deltaj.transformations.utils.ListUtils;

public class DeltaJProductsWithFeatureFinder {

	private final ProductLine productLine;
	private final Feature feature;

	public DeltaJProductsWithFeatureFinder(Feature feature) {

		this.productLine = DeltaJHierarchy.getProductLine(DeltaJHierarchy.getFeatures(feature));
		this.feature = feature;
	}

	public List<Product> find() {

		Program program = DeltaJHierarchy.getProgram(productLine);
		List<Product> products = ListFactory.createArrayList();
		for (Product product: program.getProducts()) {
			if (ListUtils.findElementByIdentity(product.getFeatures(), feature) >= 0) {
				products.add(product);
			}
		}
		return products;
	}
}
