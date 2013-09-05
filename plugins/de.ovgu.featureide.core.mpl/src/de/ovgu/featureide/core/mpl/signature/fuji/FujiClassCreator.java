package de.ovgu.featureide.core.mpl.signature.fuji;

import de.ovgu.featureide.core.mpl.signature.abstr.AClassCreator;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;

public class FujiClassCreator extends AClassCreator {
	@Override
	public FujiClass create(AbstractClassSignature sig) {
		return new FujiClass(sig);
	}
}
