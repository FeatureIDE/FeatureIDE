package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.Comparator;

public class SignatureNameComparator implements Comparator<AbstractSignature> {

	@Override
	public int compare(AbstractSignature sig0, AbstractSignature sig1) {
		return sig0.getFullName().compareTo(sig1.getFullName());
	}
}
