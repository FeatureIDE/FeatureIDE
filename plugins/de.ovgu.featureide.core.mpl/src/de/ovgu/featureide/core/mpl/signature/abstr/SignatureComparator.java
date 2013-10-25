package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.Comparator;

//TODO MPL: better implementation
public class SignatureComparator implements Comparator<Object> {

	@Override
	public int compare(Object sig0, Object sig1) {
		return buildCompareString(sig0).compareTo(buildCompareString(sig1));
	}
	
	private String buildCompareString(Object obj) {
		StringBuilder sb = new StringBuilder();
		if (obj instanceof AbstractSignature) {
			sb.append('b');
			if (obj instanceof AbstractMethodSignature) {
				sb.append('c');
			} else if (obj instanceof AbstractFieldSignature) {
				sb.append('b');
			} else if (obj instanceof AbstractClassSignature) {
				sb.append('a');
			} else {
				sb.append('d');
			}
			sb.append(((AbstractSignature)obj).name.toLowerCase());
		} else if (obj instanceof AbstractClassFragment) {
			sb.append('a');
			sb.append(((AbstractClassFragment)obj).signature.name.toLowerCase());
		}
		
		return sb.toString();
	}

}
