package de.ovgu.featureide.core.mpl.signature.abstr;

public abstract class AbstractFieldSignature extends AbstractSignature {

	protected AbstractFieldSignature(AbstractClassSignature parent, String name, String modifiers, String type) {
		super(parent, name, modifiers, type);
	}

//	protected AbstractFieldSignature(AbstractSignature orgSig, boolean ext) {
//		super(orgSig, ext);
//	}

}
