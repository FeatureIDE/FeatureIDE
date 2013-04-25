package org.deltaj.transformations.formula;

import java.util.TreeSet;
import org.deltaj.deltaj.Feature;

public class FeatureSet extends TreeSet<Feature> {

	public FeatureSet() {

		super(new FeatureComparator());
	}
}
