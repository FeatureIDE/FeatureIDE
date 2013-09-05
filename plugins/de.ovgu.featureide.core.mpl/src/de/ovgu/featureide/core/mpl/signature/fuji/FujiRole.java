package de.ovgu.featureide.core.mpl.signature.fuji;

import de.ovgu.featureide.core.mpl.signature.ViewTag;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractRole;

public class FujiRole extends AbstractRole {
	
	public FujiRole(String featureName, FujiClassSignature signature) {
		super(featureName, signature);
	}
	
	private FujiRole(FujiRole fujiRole, ViewTag viewTag) {
		super(fujiRole, viewTag);
	}

	@Override
	public String toString() {
		return FujiStringBuilder.getClassString(this, false);
	}

	@Override
	public String toShortString() {
		return FujiStringBuilder.getClassString(this, true);
	}

//	@Override
//	public FujiClass toClass() {
//		return new FujiClass(signature);
//	}

	@Override
	public FujiRole reduce(ViewTag viewTag) {
		return new FujiRole(this, viewTag);
	}
}
