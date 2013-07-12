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
package de.ovgu.featureide.core.mpl.signature;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import de.ovgu.featureide.core.mpl.JavaInterfaceProject;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractRole;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaClassCreator;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/** 
 * Maps the feature names to a list of role signatures.
 * 
 * @author Sebastian Krieter
 */
public class RoleMap {
	private final HashMap<AbstractSignature, AbstractSignature> 
		signatureSet = new HashMap<AbstractSignature, AbstractSignature>();
	private final HashMap<String, FeatureRoles> 
		featureRoleMap = new HashMap<String, FeatureRoles>();

//	private final LinkedList<AbstractSignature> 
//		childSignatures = new LinkedList<AbstractSignature>();
	
	private final JavaInterfaceProject interfaceProject;
	
	private final FeatureModel model;
	
	public RoleMap(JavaInterfaceProject interfaceProject) {
		this.interfaceProject = interfaceProject;
		this.model = interfaceProject.getFeatureModel();
	}
	
	public RoleMap(FeatureModel model) {
		this.interfaceProject = null;
		this.model = model;
	}
	
	public RoleMap(RoleMap roleMap, ViewTag viewTag) {
		this(roleMap.interfaceProject);
		for (Entry<String, FeatureRoles> rolesEntrySet : roleMap.featureRoleMap.entrySet()) {
			FeatureRoles reducedRoles = getRoles(rolesEntrySet.getKey());
			for (AbstractRole role : rolesEntrySet.getValue()) {
				if (role.getSignature().hasViewTag(viewTag)){
					reducedRoles.add(role.reduce(viewTag));					
				}
			}
		}
	}
	
	public RoleMap(RoleMap roleMap) {
		this(roleMap, null);
	}
	
	public void addRole(AbstractRole role) {
		String s = role.getFeatureName();
		getRoles(s).add(role);
	}
	
	public FeatureRoles getRoles(String featurename) {
		return getRoles(model.getFeature(featurename));
	}
	
	public FeatureRoles getRoles(Feature feature) {
		FeatureRoles ret = featureRoleMap.get(feature.getName());
		if (ret == null) {
			ret = new FeatureRoles(feature);
			featureRoleMap.put(feature.getName(), ret);
		}
		return ret;
	}

//	public ProjectSignature generateSignature2(List<String> featureList, ViewTag viewTag) {
//		ProjectSignature javaSig = new ProjectSignature(viewTag);
//		
//		if (featureList == null) {
//			for (FeatureRoles roles : featureRoleMap.values()) {
//				for (AbstractRole role : roles) {
//					javaSig.addRole(role);
//				}
//			}
//		} else {
//			for (String featureName : featureList) {
//				FeatureRoles roles = featureRoleMap.get(featureName);
//				if (roles != null) {
//					for (AbstractRole role : roles) {
//						javaSig.addRole(role);
//					}
//				}
//			}
//		}
//		return javaSig;
//	}
	
	public ProjectSignature generateSignature() {
		return generateSignature(null, null);
	}
	
	public ProjectSignature generateSignature(List<String> featureList) {
		return generateSignature(featureList, null);
	}
	
	public ProjectSignature generateSignature(ViewTag viewTag) {
		return generateSignature(null, viewTag);
	}
	
	public ProjectSignature generateSignature(List<String> featureList, ViewTag viewTag) {
		ProjectSignature javaSig = new ProjectSignature(viewTag, false);
		javaSig.setaClassCreator(new JavaClassCreator());
		
		if (featureList == null) {
			for (AbstractSignature sig : signatureSet.keySet()) {
				javaSig.addSignature(sig);
			}
		} else {
			for (AbstractSignature sig : signatureSet.keySet()) {
				for (String feature : featureList) {
					if (sig.getFeatures().contains(feature)) {
						javaSig.addSignature(sig);
						break;
					}
				}
			}
		}
		return javaSig;
	}
	
	public String getStatisticsString() {
		final int[][] allCounters = new int[4][4];
		
		for (AbstractSignature signature : signatureSet.keySet()) {
			if (signature instanceof AbstractFieldSignature) {
				count(signature, allCounters[2]);
			} else if (signature instanceof AbstractMethodSignature) {
				count(signature, allCounters[3]);
			} else if (signature instanceof AbstractClassSignature) {
				if (signature.getParent() != null) {
					count(signature, allCounters[1]);
				} else {
					count(signature, allCounters[0]);
				}
			}
		}

		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < allCounters.length; i++) {
			int[] curCounter = allCounters[i];
			switch (i) {
			case 0: sb.append("#Classes: "); break;
			case 1: sb.append("#InnerClasses: "); break;
			case 2: sb.append("#Fields: "); break;
			case 3: sb.append("#Metohds: "); break;
			}
			sb.append(curCounter[0]);
			sb.append("\n\t#Private: ");
			sb.append(curCounter[2]);
			sb.append("\n\t#Definitions: ");
			sb.append(curCounter[1]);
			sb.append("\n\t\t#Private Definitions: ");
			sb.append(curCounter[3]);
			sb.append('\n');
		}
		return sb.toString();
	}
	
	private void count(AbstractSignature signature, int[] curCounter) {
		curCounter[0]++;
		curCounter[1] += signature.getFeatures().size();
		if (signature.isPrivate()) {
			curCounter[2]++;
			curCounter[3] += signature.getFeatures().size();
		}
	}

	@Deprecated
	public void addDefaultViewTag(String name) {
		final ViewTag 
			classViewTag = interfaceProject.getViewTagPool().getViewTag(name, 3),
			methodViewTag = interfaceProject.getViewTagPool().getViewTag(name, 2),
			fieldViewTag = interfaceProject.getViewTagPool().getViewTag(name, 1);
		
		for (AbstractSignature signature : signatureSet.keySet()) {
			if (signature instanceof AbstractFieldSignature) {
				signature.addViewTag(fieldViewTag);
			} else if (signature instanceof AbstractMethodSignature) {
				signature.addViewTag(methodViewTag);
			} else if (signature instanceof AbstractClassSignature) {
				signature.addViewTag(classViewTag);
			}
		}
	}

	public AbstractSignature getSignatureRef(AbstractSignature sig) {
		AbstractSignature sigRef = signatureSet.get(sig);
		if (sigRef == null) {
			signatureSet.put(sig, sig);
			return sig;
		} else {
			return sigRef;
		}
	}
	
	public Collection<AbstractSignature> getSignatures() {
		return signatureSet.keySet();
	}	
}
