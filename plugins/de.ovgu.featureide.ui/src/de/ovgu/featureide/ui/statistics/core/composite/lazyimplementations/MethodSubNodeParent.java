package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class MethodSubNodeParent extends Parent {

	private final FSTMethod method;

	public MethodSubNodeParent(String descString, FSTMethod method) {
		super(descString.replace(":", ""));
		this.method = method;
	}

	public FSTMethod getMethod() {
		return method;
	}	

}
