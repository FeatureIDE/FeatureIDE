package de.ovgu.featureide.core.mpl.signature.filter;

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;

public class MemberFilter implements ISignatureFilter {
	@Override
	public boolean isValid(AbstractSignature signature) {
		return !(signature instanceof AbstractClassSignature);
	}
}
