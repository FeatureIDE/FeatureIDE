package org.deltaj.transformations.utils;

import java.util.Set;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.Program;
import org.deltaj.transformations.formula.FeatureSet;

public class GrammarUtils {

	public static Program getProgram(DeltaModule deltaModule) {

		return (Program) deltaModule.eContainer();
	}

	public static DeltaPartition getPartition(PartitionPart partitionPart) {

		return (DeltaPartition) partitionPart.eContainer();
	}

	public static DeltaPartition getPartition(ModuleReference moduleReference) {

		return getPartition(getPartitionPart(moduleReference));
	}

	private static PartitionPart getPartitionPart(ModuleReference moduleReference) {

		return (PartitionPart) moduleReference.eContainer();
	}

	public static Program getProgram(Product product) {

		return (Program) product.eContainer();
	}

	public static Set<Feature> getFeatures(Product product) {

		Set<Feature> features = new FeatureSet();

		for (Feature feature: product.getFeatures()) {
			features.add(feature);
		}

		return features;
	}
}
