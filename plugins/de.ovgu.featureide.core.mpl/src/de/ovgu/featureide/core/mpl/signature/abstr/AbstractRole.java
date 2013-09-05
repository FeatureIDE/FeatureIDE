package de.ovgu.featureide.core.mpl.signature.abstr;

import java.util.HashMap;
import java.util.HashSet;

import de.ovgu.featureide.core.mpl.signature.ViewTag;

public abstract class AbstractRole extends AbstractClassFragment {

	protected final String featureName;
	
	protected AbstractRole(String featureName, AbstractClassSignature signature) {
		super(signature);
		this.featureName = featureName;
		
		members = new HashSet<AbstractSignature>();
		innerClasses = new HashMap<String, AbstractClassFragment>();
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
				innerClasses.put(innerClass.getSignature().getFullName(), 
						((AbstractRole)innerClass).reduce(viewTag));
			}
		}
	}

	public String getFeatureName() {
		return featureName;
	}

//	public abstract AbstractClass toClass();
	public abstract AbstractRole reduce(ViewTag viewTag);
}
