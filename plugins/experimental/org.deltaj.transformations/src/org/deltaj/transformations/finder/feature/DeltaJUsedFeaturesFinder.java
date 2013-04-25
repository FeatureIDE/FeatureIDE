package org.deltaj.transformations.finder.feature;

import java.util.Set;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.SetFactory;

public class DeltaJUsedFeaturesFinder {

	private final Program program;
	private final ProductLine productLine;
	private final Set<Feature> usedFeatures;

	public DeltaJUsedFeaturesFinder(Program program) {

		this.program = program;
		this.productLine = null;
		this.usedFeatures = SetFactory.createIdentityHashSet();
	}

	public DeltaJUsedFeaturesFinder(ProductLine productLine) {

		this.program = DeltaJHierarchy.getProgram(productLine);
		this.productLine = productLine;
		this.usedFeatures = SetFactory.createIdentityHashSet();
	}

	public Set<Feature> find() {

		usedFeatures.clear();

		for (Product product: program.getProducts()) {
			addFeatures(product);
		}

		return usedFeatures;
	}

	private void addFeatures(Product product) {

		if (productLine == null || product.getProductLine() == productLine) {
			for (Feature feature: product.getFeatures()) {
				usedFeatures.add(feature);
			}
		}
	}
}
