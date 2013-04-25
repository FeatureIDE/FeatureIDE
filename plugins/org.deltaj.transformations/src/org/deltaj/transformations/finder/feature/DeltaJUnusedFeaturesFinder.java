package org.deltaj.transformations.finder.feature;

import java.util.Set;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.utils.SetFactory;

public class DeltaJUnusedFeaturesFinder {

	private final Set<Feature> declaredFeatures;

	public DeltaJUnusedFeaturesFinder() {

		this.declaredFeatures = SetFactory.createIdentityHashSet();
	}

	public Set<Feature> find(Program program) {

		declaredFeatures.clear();
		collectFeatures(program);
		declaredFeatures.removeAll(new DeltaJUsedFeaturesFinder(program).find());

		return declaredFeatures;
	}

	private void collectFeatures(Program program) {

		for (ProductLine productLine: program.getProductLines()) {
			collectFeatures(productLine);
		}
	}

	public Set<Feature> find(ProductLine productLine) {

		declaredFeatures.clear();
		collectFeatures(productLine);
		declaredFeatures.removeAll(new DeltaJUsedFeaturesFinder(productLine).find());

		return declaredFeatures;
	}

	private void collectFeatures(ProductLine productLine) {

		declaredFeatures.addAll(productLine.getFeatures().getFeaturesList());
	}
}
