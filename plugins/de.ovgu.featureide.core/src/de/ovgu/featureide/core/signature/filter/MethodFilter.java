package de.ovgu.featureide.core.signature.filter;

import de.ovgu.featureide.core.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature;

public class MethodFilter implements ISignatureFilter {

	@Override
	public boolean isValid(AbstractSignature signature) {
		return signature instanceof AbstractMethodSignature;
	}
}
