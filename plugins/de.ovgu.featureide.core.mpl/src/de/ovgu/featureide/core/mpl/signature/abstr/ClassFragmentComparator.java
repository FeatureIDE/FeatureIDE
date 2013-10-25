package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.Comparator;

//TODO MPL: better implementation
public class ClassFragmentComparator implements Comparator<AbstractClassFragment> {

	private final String favoritClass;
	
	public ClassFragmentComparator(String favoritClass) {
		if (favoritClass == null) {
			this.favoritClass = "";
		} else {
			this.favoritClass = favoritClass.toLowerCase();
		}
	}

	@Override
	public int compare(AbstractClassFragment sig0, AbstractClassFragment sig1) {
		return buildCompareString(sig0).compareTo(buildCompareString(sig1));
	}
	
	private String buildCompareString(AbstractClassFragment frag) {
		String sigClassName;
		AbstractClassSignature parentSig = frag.signature.parent;
		if (parentSig != null) {
			while(parentSig.parent != null) {
				parentSig = parentSig.parent;
			}
			sigClassName = parentSig.name;
		} else {
			sigClassName = frag.signature.name;
		}
		
		return (sigClassName.toLowerCase().equals(favoritClass) ? 'a' : 'b') + frag.signature.name.toLowerCase();
	}
}
