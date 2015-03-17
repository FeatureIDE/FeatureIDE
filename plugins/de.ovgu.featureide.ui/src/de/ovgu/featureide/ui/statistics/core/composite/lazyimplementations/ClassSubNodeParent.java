package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class ClassSubNodeParent extends Parent {

	private FSTClassFragment frag;
	private FSTClass fstClass;
	
	public ClassSubNodeParent(String descString, FSTClassFragment fstClassFrag) {
		super(descString.replace(":", ""));
		frag = fstClassFrag;
	}
	
	public ClassSubNodeParent(String descString, FSTClass fstClass) {
		super(descString.replace(":", ""));
		this.fstClass = fstClass;
	}

	public FSTClassFragment getFragment(){
		return frag;
	}
	
	public FSTClass getFSTClass(){
		return fstClass;
	}
	
}
