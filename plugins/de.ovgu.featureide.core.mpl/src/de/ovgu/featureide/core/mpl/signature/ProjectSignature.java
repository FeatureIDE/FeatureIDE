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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import de.ovgu.featureide.core.mpl.signature.abstr.AClassCreator;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractRole;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;

/** 
 * Holds the signature information for a whole java project.
 * 
 * @author Sebastian Krieter
 */
public class ProjectSignature {

	protected final HashMap<AbstractClassSignature, AbstractClassFragment> classList = new HashMap<AbstractClassSignature, AbstractClassFragment>();
	protected final ViewTag viewTag;
	
	protected int hashCode = 0;
	protected boolean hasHashCode = false;

	public ProjectSignature(ViewTag viewTag) {
		this.viewTag = viewTag;
	}
	
	public ProjectSignature() {
		this(null);
	}

	public ViewTag getViewTag() {
		return viewTag;
	}
	
	public AbstractClassFragment getClass(AbstractClassSignature id) {
		return classList.get(id);
	}
	
	public Collection<AbstractClassFragment> getClasses() {
		return classList.values();
	}
	
	private void addClass(AbstractClassFragment classSig) {
		classList.put(classSig.getSignature(), classSig);
	}
	
//	public void addRole(AbstractRole role) {
//		AbstractClassSignature roleSig = role.getSignature();
//		if (roleSig.hasViewTag(viewTag)) {
//			hasHashCode = false;
//			AbstractClassFragment aClass = getClass(roleSig);
//			if (aClass == null) {
//				aClass = role.toClass();
//				addClass(aClass);
//			}
//			for (AbstractSignature member : role.getMembers()) {
//				if (member.hasViewTag(viewTag)) {
//					aClass.addMember(member);
//				}
//			}
//			for (AbstractClassFragment innerClass : role.getInnerClasses().values()) {
//				if (innerClass.getSignature().hasViewTag(viewTag)) {
//					aClass.addInnerClass(innerClass, viewTag);
//				}
//			}
//			for (String imp : role.getSignature().getImportList()) {
//				aClass.getSignature().addImport(imp);
//			}
//		}
//	}
	
	public void addRole(AbstractRole role) {
		addRoleRec(role, null);
	}
	
	private void addRoleRec(AbstractRole role, AbstractClassFragment parent) {
		AbstractClassSignature roleSig = role.getSignature();
		if (roleSig.hasViewTag(viewTag)) {
			hasHashCode = false;
			AbstractClassFragment aClass = (parent == null)
					? getClass(roleSig)
					: parent.getInnerClass(roleSig);
					
			if (aClass == null) {
				aClass = role.toClass();
				if (parent == null) {
					addClass(aClass);
				} else {
					parent.addInnerClass(aClass);
				}
			}
			for (AbstractSignature member : role.getMembers()) {
				if (member.hasViewTag(viewTag)) {
					aClass.addMember(member);
				}
			}
			for (AbstractClassFragment innerClass : role.getInnerClasses().values()) {
				addRoleRec((AbstractRole) innerClass, aClass);
			}
//			for (String imp : roleSig.getImportList()) {
//				aClass.getSignature().addImport(imp);
//			}
		}
	}

	private AClassCreator aClassCreator = null;

	public void setaClassCreator(AClassCreator aClassCreator) {
		this.aClassCreator = aClassCreator;
	}

	public void addSignature(AbstractSignature sig) {
//		if (sig.hasViewTag(viewTag)) {
//			LinkedList<AbstractClassSignature> parents = new LinkedList<AbstractClassSignature>();
//			AbstractClassSignature parent = sig.getParent();
//			while (parent != null) {
//				if (!parent.hasViewTag(viewTag)) {
//					return;
//				}
//				parents.add(parent);
//				parent = parent.getParent();
//			}
//			if (!parents.isEmpty()) {
//				parent = parents.removeLast();
//				AbstractClassFragment parentClass = getClass(parent);
//				if (parentClass == null) {
//					parentClass = aClassCreator.create(parent);
//					addClass(parentClass);
//				}
//				for (AbstractClassSignature abstractClassSignature : parents) {
//					AbstractClassFragment parentClass = (parent == null) getClass(parent);
//					if (parentClass == null) {
//						parentClass = aClassCreator.create(parent);
//						addClass(parentClass);
//					}
//				}
//			}
//			
//			if (sig instanceof AbstractClassSignature) {
//				
//			}
//			classList.put(parent, parentClass);
//			parentClass = aClassCreator.create(parent);
//			
//			AbstractClassSignature parent = sig.getParent();
//			if (parent != null && parent.hasViewTag(viewTag)) {
//				AbstractClassFragment parentClass = aClassCreator.create(parent);
//				parentClass.addMember(sig);
//				while (parent.getParent() != null) {
//					AbstractClassSignature child = parent;
//					parent = parent.getParent();
//					if (!parent.hasViewTag(viewTag)) {
//						return;
//					}
//					parentClass = aClassCreator.create(parent);
//
//					parentClass.addMember(child);
//				}
//				classList.put(parent, parentClass);
//			}
//		}
		
	}

	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		
		ProjectSignature otherSig = (ProjectSignature) obj;
		
		if (otherSig == null 
				|| classList.size() != otherSig.classList.size()) {
			return false;
		}
		for (Entry<AbstractClassSignature, AbstractClassFragment> entrySet : classList.entrySet()) {
			AbstractClassFragment otherClassSig = otherSig.classList.get(entrySet.getKey());
			if (otherClassSig == null || !otherClassSig.equals(entrySet.getValue())) {
				return false;
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		if (!hasHashCode) {
//			final int prime = 31;
			hashCode = 1;
			for (AbstractClassFragment cls : classList.values()) {
//				hashCode = prime * hashCode + cls.hashCode();
				hashCode = hashCode + cls.hashCode();
			}
			hasHashCode = true;
		}
		return hashCode;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (AbstractClassFragment cls : classList.values()) {
			sb.append(cls.toString());
		}
		return sb.toString();
	}

	public double similarityTo(ProjectSignature otherSig) {
		int[] countedMembers = countEqMembers(classList, otherSig.classList);
		double eqMemberCount = (double) countedMembers[0];
		double memberCount = (double) countedMembers[1];
		
		final int rf = 1000;

		return (memberCount == 0) ? 1 : Math.floor(rf * eqMemberCount / memberCount) / rf;
	}
	
	private int[] countEqMembers(Map<AbstractClassSignature, AbstractClassFragment> thisClassSigMap, Map<AbstractClassSignature, AbstractClassFragment> otherClassSigMap) {		
		int memberCount = 0, eqMemberCount = 0;
		
		if (!thisClassSigMap.isEmpty() && !otherClassSigMap.isEmpty()) {
			final HashSet<AbstractClassSignature> ids = new HashSet<AbstractClassSignature>(thisClassSigMap.keySet());
			ids.addAll(otherClassSigMap.keySet());
			memberCount += ids.size();
			
			for (AbstractClassSignature id : ids) {
				final AbstractClassFragment 
					thisClassSig = thisClassSigMap.get(id),
					otherClassSig = otherClassSigMap.get(id);
				if (thisClassSig == null) {
					memberCount += otherClassSig.getMemberCount();
				} else if (otherClassSig == null) {
					memberCount += thisClassSig.getMemberCount();
				} else {
					eqMemberCount++;
					
					final HashSet<AbstractSignature> members = new HashSet<AbstractSignature>(thisClassSig.getMembers());
					memberCount += members.size();
					
					for (AbstractSignature otherMember : otherClassSig.getMembers()) {
						if (members.add(otherMember)) {
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
			final Map<AbstractClassSignature, AbstractClassFragment> classSigMap;
			if (!thisClassSigMap.isEmpty()) {
				classSigMap = thisClassSigMap;
			} else if (!otherClassSigMap.isEmpty()) {
				classSigMap = otherClassSigMap;
			} else {
				classSigMap = null;
			}
			if (classSigMap != null) {
				memberCount += classSigMap.size();
				for (AbstractClassFragment classSig : classSigMap.values()) {
					memberCount += classSig.getMemberCount();
				}
			}
		}
		
		return new int[]{eqMemberCount, memberCount};
	}
}
