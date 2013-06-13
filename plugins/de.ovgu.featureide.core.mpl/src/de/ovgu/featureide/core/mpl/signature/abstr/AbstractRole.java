package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.HashMap;
import java.util.LinkedList;

import de.ovgu.featureide.core.mpl.signature.ViewTag;

public abstract class AbstractRole extends AbstractClassFragment {

	protected final String featureName;
	
	protected AbstractRole(String featureName, AbstractClassSignature signature) {
		super(signature);
		this.featureName = featureName;
		
		members = new LinkedList<AbstractSignature>();
		innerClasses = new HashMap<AbstractClassSignature, AbstractClassFragment>();
	}
	
	protected AbstractRole(AbstractRole role, ViewTag viewTag) {
		this(role.featureName, role.signature);
		
		for (AbstractSignature member : role.members) {
			if (member.hasViewTag(viewTag)) {
				members.add(member);
			}
		}
		for (AbstractClassFragment innerClass : role.innerClasses.values()) {
			if (innerClass.signature.hasViewTag(viewTag)) {
				innerClasses.put(innerClass.getSignature(), 
						((AbstractRole)innerClass).reduce(viewTag));
			}
		}
	}

	public String getFeatureName() {
		return featureName;
	}

//	@Override
//	public void addInnerClass(AbstractClassFragment innerClass) {
////		if (innerClass instanceof AbstractRole) {
//			super.addInnerClass(innerClass);
////		}
//	}

	public abstract AbstractClass toClass();
	public abstract AbstractRole reduce(ViewTag viewTag);
}
