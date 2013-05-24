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
package de.ovgu.featureide.core.mpl.signature.java;

import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import de.ovgu.featureide.core.mpl.JavaInterfaceProject;
import de.ovgu.featureide.core.mpl.signature.ViewTag;
import de.ovgu.featureide.fm.core.Feature;

/** 
 * Maps the feature names to a list of role signatures.
 * 
 * @author Sebastian Krieter
 */
public class JavaRoleMap {
	private final HashMap<String, JavaFeatureSignature> featureRoleMap = new HashMap<String, JavaFeatureSignature>();
	private final JavaInterfaceProject interfaceProject;
	
	public JavaRoleMap(JavaInterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
	}
	
	public JavaRoleMap(JavaRoleMap roleMap, ViewTag viewTag) {
		this(roleMap.interfaceProject);
		
		for (Entry<String, JavaFeatureSignature> rolesEntrySet : roleMap.featureRoleMap.entrySet()) {
			JavaFeatureSignature reducedRoles = getRoles(rolesEntrySet.getKey());
			for (JavaRoleSignature role : rolesEntrySet.getValue()) {
				if (role.hasViewTag(viewTag)){
					reducedRoles.add(new JavaRoleSignature(role, viewTag));					
				}
			}
		}
	}
	
	public JavaRoleMap(JavaRoleMap roleMap) {
		this(roleMap, null);
	}
	
	public void addRole(JavaRoleSignature role) {
		getRoles(role.getFeatureName()).add(role);
	}
	
	public JavaFeatureSignature getRoles(String featurename) {
		JavaFeatureSignature ret = featureRoleMap.get(featurename);
		if (ret == null) {
			ret = new JavaFeatureSignature(interfaceProject.getFeatureModel().getFeature(featurename));
			featureRoleMap.put(featurename, ret);
		}
		return ret;
	}
	
	public JavaFeatureSignature getRoles(Feature feature) {
		return getRoles(feature.getName());
	}

	public JavaSignature generateSignature(List<String> featureList, ViewTag viewTag) {
		JavaSignature javaSig = new JavaSignature(viewTag);
		
		if (featureList == null) {
			for (JavaFeatureSignature roles : featureRoleMap.values()) {
				for (JavaRoleSignature role : roles) {
					javaSig.addRole(role);
				}
			}
		} else {
			for (String featureName : featureList) {
				JavaFeatureSignature roles = featureRoleMap.get(featureName);
				if (roles != null) {
					for (JavaRoleSignature role : roles) {
						javaSig.addRole(role);
					}
				}
			}
		}
		return javaSig;
	}
	
	public JavaSignature generateSignature() {
		return generateSignature(null, null);
	}
	
	public JavaSignature generateSignature(List<String> featureList) {
		return generateSignature(featureList, null);
	}
	
	public JavaSignature generateSignature(ViewTag viewTag) {
		return generateSignature(null, viewTag);
	}
	
	@Deprecated
	public void addDefaultViewTag(String name) {
		final ViewTag 
			classViewTag = interfaceProject.getViewTagPool().getViewTag(name, 3),
			methodViewTag = interfaceProject.getViewTagPool().getViewTag(name, 2),
			fieldViewTag = interfaceProject.getViewTagPool().getViewTag(name, 1);
		
		for (JavaFeatureSignature roles : featureRoleMap.values()) {
			for (JavaRoleSignature role : roles) {
				role.addDefaultViewTag(classViewTag, methodViewTag, fieldViewTag);
			}
		}
	}
}
