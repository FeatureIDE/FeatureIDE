package de.ovgu.featureide.core.mpl.signature.java;

import de.ovgu.featureide.core.mpl.signature.abstr.AClassCreator;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;

public class JavaClassCreator extends AClassCreator {
	@Override
	public JavaClass create(AbstractClassSignature sig) {
		return new JavaClass(sig);
	}
}
