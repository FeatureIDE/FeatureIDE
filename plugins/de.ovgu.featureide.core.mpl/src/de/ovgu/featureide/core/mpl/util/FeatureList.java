package de.ovgu.featureide.core.mpl.util;

import java.util.HashSet;

public class FeatureList extends HashSet<String> {
	private static final long serialVersionUID = 1L;
	private static final int hashCodePrime = 31;
	
	private int hashCode = 0;

	@Override
	public boolean add(String arg0) {
		if (super.add(arg0)) {
			hashCode *= hashCodePrime;
			hashCode += arg0.hashCode();
			
			return true;
		}
		return false;
	}

//	@Override
//	public boolean equals(Object o) {
//		return super.equals(o);
//	}

	@Override
	public int hashCode() {
		return hashCode;
	}
}
