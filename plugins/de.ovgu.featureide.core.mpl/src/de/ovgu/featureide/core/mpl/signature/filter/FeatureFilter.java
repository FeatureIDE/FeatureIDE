package de.ovgu.featureide.core.mpl.signature.filter;

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;

public class FeatureFilter implements ISignatureFilter {
	private final int[] featureList;
	
	public FeatureFilter(int[] featureList) {
		this.featureList = featureList;
	}

	@Override
	public boolean isValid(AbstractSignature signature) {
		return signature.hasFeature(featureList);
	}
}
