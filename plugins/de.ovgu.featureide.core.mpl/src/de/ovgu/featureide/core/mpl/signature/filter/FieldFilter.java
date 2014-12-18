package de.ovgu.featureide.core.mpl.signature.filter;

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;

public class FieldFilter implements ISignatureFilter {

	@Override
	public boolean isValid(AbstractSignature signature) {
		return signature instanceof AbstractFieldSignature;
	}
}
