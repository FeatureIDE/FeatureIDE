package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.Iterator;
import java.util.LinkedList;

public abstract class AbstractMethodSignature extends AbstractSignature {
	
	protected final LinkedList<String> parameterTypes;
	protected final boolean isConstructor;
	
	protected AbstractMethodSignature(AbstractClassSignature parent, String name, String modifier, String type, LinkedList<String> parameterTypes, boolean isConstructor) {
		super(parent, name, modifier, type, null);
		this.isConstructor = isConstructor;
		this.parameterTypes = parameterTypes;
	}
	
	protected AbstractMethodSignature(AbstractMethodSignature orgSig, boolean ext) {
		super(orgSig, ext);
		isConstructor = orgSig.isConstructor;
		parameterTypes = new LinkedList<String>(orgSig.parameterTypes);
	}

	public LinkedList<String> getParameterTypes() {
		return parameterTypes;
	}

	public boolean isConstructor() {
		return isConstructor;
	}

	@Override
	protected void computeHashCode() {
		super.computeHashCode();
		hashCode = hashCodePrime * hashCode + (isConstructor ? 1231 : 1237);
		for (String parameter : parameterTypes) {
			hashCode = hashCodePrime * hashCode + parameter.hashCode();
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		
		AbstractMethodSignature otherSig = (AbstractMethodSignature) obj;
		
		if (!super.sigEquals(otherSig)) 
			return false;
		if (isConstructor != otherSig.isConstructor 
				|| parameterTypes.size() != otherSig.parameterTypes.size()) {
			return false;
		}

		Iterator<String> otherParameterIt = otherSig.parameterTypes.iterator();
		Iterator<String> thisParameterIt = parameterTypes.iterator();
		while (thisParameterIt.hasNext()) {
			if (!thisParameterIt.next().equals(otherParameterIt.next())) {
				return false;
			}
		}
		return true;
	}
}
