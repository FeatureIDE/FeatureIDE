package org.deltaj.transformations.formula;

import java.util.Comparator;
import org.deltaj.deltaj.Feature;

public class FeatureComparator implements Comparator<Feature> {

	@Override
	public int compare(Feature left, Feature right) {

		return left.getName().compareTo(right.getName());
	}
}
