/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
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
