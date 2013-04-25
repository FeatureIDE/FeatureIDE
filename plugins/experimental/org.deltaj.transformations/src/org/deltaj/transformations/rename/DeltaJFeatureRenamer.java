package org.deltaj.transformations.rename;

import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.transformations.finder.feature.DeltaJFeatureFinder;
import org.deltaj.transformations.finder.feature.references.DeltaJFeatureReferencesFinder;
import org.deltaj.transformations.utils.DeltaJHierarchy;
import org.deltaj.transformations.utils.ListUtils;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.eclipse.emf.common.util.EList;

public class DeltaJFeatureRenamer {

	private final ProductLine productLine;
	private final Feature feature;
	private final String newName;

	public DeltaJFeatureRenamer(Feature feature, String newName) {

		this.productLine = DeltaJHierarchy.getProductLine(feature);
		this.feature = feature;
		this.newName = newName;
	}

	public void rename() {

		checkName();

		feature.setName(newName);

		for (FeatureRef featureReference: new DeltaJFeatureReferencesFinder(feature).find()) {
			featureReference.setFeature(null);
			featureReference.setFeature(feature);
		}

		for (Product product: DeltaJHierarchy.getProgram(productLine).getProducts()) {
			EList<Feature> featureList = product.getFeatures();
			int index = ListUtils.findElementByIdentity(featureList, feature);
			if (index >= 0) {
				featureList.remove(index);
				featureList.add(index, feature);
			}
		}
	}

	private void checkName() {

		Feature otherFeature = new DeltaJFeatureFinder(productLine, newName).find();

		if (otherFeature != null) {
			throw new DeltaJException("A feature with the name '%s' already exists.", newName);
		}
	}
}
