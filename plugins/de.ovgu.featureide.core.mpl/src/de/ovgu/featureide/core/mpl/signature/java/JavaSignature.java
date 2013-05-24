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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.ovgu.featureide.core.mpl.signature.ViewTag;

/** 
 * Holds the signature information for whole java project.
 * 
 * @author Sebastian Krieter
 */
public class JavaSignature {

	private final HashMap<String, JavaClassSignature> classList = new HashMap<String, JavaClassSignature>();
	private final ViewTag viewTag;
	
	private int hashCode = 0;
	private boolean hasHashCode = false;

	public JavaSignature(ViewTag viewTag) {
		this.viewTag = viewTag;
	}
	
	public JavaSignature() {
		this(null);
	}

	public ViewTag getViewTag() {
		return viewTag;
	}
	
	public JavaClassSignature getClass(String id) {
		return classList.get(id);
	}
	
	public Collection<JavaClassSignature> getClasses() {
		return classList.values();
	}
	
	private void addClass(JavaClassSignature classSig) {
		classList.put(classSig.getFullName(), classSig);
		hasHashCode = false;
	}
	
	public void addRole(JavaRoleSignature roleSig) {
		if (roleSig.hasViewTag(viewTag)) {
			JavaClassSignature classSig = getClass(roleSig.getFullName());
			if (classSig == null) {
				classSig = roleSig.toJavaClass();
				addClass(classSig);
			}
			
			for (JavaFieldSignature field : roleSig.getFields()) {
				if (field.hasViewTag(viewTag)) {
					classSig.addField(field);
				}
			}
			for (JavaMethodSignature method : roleSig.getMethods()) {
				if (method.hasViewTag(viewTag)) {
					classSig.addMethod(method);
				}
			}
			for (JavaRoleSignature innerClass : roleSig.getInnerClasses().values()) {
				if (innerClass.hasViewTag(viewTag)) {
					classSig.addInnerClass(innerClass.toJavaClass());
				}
			}
			for (String imp : roleSig.getImportList()) {
				classSig.addImport(imp);
			}
			for (String extend : roleSig.getExtendList()) {
				classSig.addExtend(extend);
			}
			for (String implement : roleSig.getImplementList()) {
				classSig.addImplement(implement);
			}
		}
	}

	@Override
	public boolean equals(Object obj) {
		JavaSignature otherSig = (JavaSignature) obj;
		
		if (classList.size() != otherSig.classList.size()) {
			return false;
		}
		for (Entry<String, JavaClassSignature> entrySet : classList.entrySet()) {
			JavaClassSignature otherClassSig = otherSig.classList.get(entrySet.getKey());
			if (otherClassSig == null || !otherClassSig.equals(entrySet.getValue())) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		if (!hasHashCode) {
			for (JavaClassSignature cls : classList.values()) {
				hashCode += cls.hashCode();
			}
			hasHashCode = true;
		}
		return hashCode;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (JavaClassSignature cls : classList.values()) {
			sb.append(cls.toString());
		}
		return sb.toString();
	}

	public double similarityTo(JavaSignature otherSig) {
		int[] countedMembers = countEqMembers(classList, otherSig.classList);
		double eqMemberCount = (double) countedMembers[0];
		double memberCount = (double) countedMembers[1];
		
		final int rf = 1000;

		return (memberCount == 0) ? 1 : Math.floor(rf * eqMemberCount / memberCount) / rf;
	}
	
	private int[] countEqMembers(Map<String, JavaClassSignature> thisClassSigMap, Map<String, JavaClassSignature> otherClassSigMap) {		
		int memberCount = 0, eqMemberCount = 0;
		
		if (!thisClassSigMap.isEmpty() && !otherClassSigMap.isEmpty()) {
			final HashSet<String> ids = new HashSet<String>(thisClassSigMap.keySet());
			ids.addAll(otherClassSigMap.keySet());
			memberCount += ids.size();
			
			for (String id : ids) {
				final JavaClassSignature 
					thisClassSig = thisClassSigMap.get(id),
					otherClassSig = otherClassSigMap.get(id);
				if (thisClassSig == null) {
					memberCount += otherClassSig.getMemberCount();
				} else if (otherClassSig == null) {
					memberCount += thisClassSig.getMemberCount();
				} else {
					eqMemberCount++;
					
					final HashSet<JavaFieldSignature> fields = new HashSet<JavaFieldSignature>(thisClassSig.getFields());
					memberCount += fields.size();
					
					for (JavaFieldSignature otherField : otherClassSig.getFields()) {
						if (fields.add(otherField)) {
							memberCount++;
						} else {
							eqMemberCount++;
						}
					}
					
					final HashSet<JavaMethodSignature> methods = new HashSet<JavaMethodSignature>(thisClassSig.getMethods());
					memberCount += methods.size();
					
					for (JavaMethodSignature otherMethod : otherClassSig.getMethods()) {
						if (methods.add(otherMethod)) {
							memberCount++;
						} else {
							eqMemberCount++;
						}
					}
					
					int[] countedMembers = countEqMembers(thisClassSig.getInnerClasses(), otherClassSig.getInnerClasses());
					eqMemberCount += countedMembers[0];
					memberCount += countedMembers[1];
				}
			}
		} else {
			final Map<String, JavaClassSignature> classSigMap;
			if (!thisClassSigMap.isEmpty()) {
				classSigMap = thisClassSigMap;
			} else if (!otherClassSigMap.isEmpty()) {
				classSigMap = otherClassSigMap;
			} else {
				classSigMap = null;
			}
			if (classSigMap != null) {
				memberCount += classSigMap.size();
				for (JavaClassSignature classSig : classSigMap.values()) {
					memberCount += classSig.getMemberCount();
				}
			}
		}
		
		return new int[]{eqMemberCount, memberCount};
	}
}
