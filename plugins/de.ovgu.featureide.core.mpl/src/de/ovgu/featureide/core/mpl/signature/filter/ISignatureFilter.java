package de.ovgu.featureide.core.mpl.signature.filter;

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;

public interface ISignatureFilter {
	public boolean isValid(AbstractSignature signature);
}
