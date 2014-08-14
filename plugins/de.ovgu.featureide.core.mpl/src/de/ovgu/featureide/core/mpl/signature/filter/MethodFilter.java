package de.ovgu.featureide.core.mpl.signature.filter;

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;

public class MethodFilter implements ISignatureFilter {

	@Override
	public boolean isValid(AbstractSignature signature) {
		return signature instanceof AbstractMethodSignature;
	}
}
