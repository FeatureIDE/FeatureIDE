package de.ovgu.featureide.core.mpl.signature.filter;

import de.ovgu.featureide.core.mpl.signature.ViewTag;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;

public class ViewTagFilter implements ISignatureFilter {
	private final ViewTag viewTag;

	public ViewTagFilter(ViewTag viewTag) {
		this.viewTag = viewTag;
	}

	@Override
	public boolean isValid(AbstractSignature signature) {
		return signature.hasViewTag(viewTag);
	}

}
