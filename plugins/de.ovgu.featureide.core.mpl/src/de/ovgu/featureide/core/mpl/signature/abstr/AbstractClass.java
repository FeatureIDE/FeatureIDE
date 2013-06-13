package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.HashMap;
import java.util.HashSet;

public abstract class AbstractClass extends AbstractClassFragment {

	protected AbstractClass(AbstractClassSignature signature) {
		super(signature);
		
		members = new HashSet<AbstractSignature>();
		innerClasses = new HashMap<String, AbstractClassFragment>();
	}
}
