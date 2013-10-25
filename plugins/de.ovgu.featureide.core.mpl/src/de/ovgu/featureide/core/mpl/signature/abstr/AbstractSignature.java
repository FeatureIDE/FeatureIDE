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

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;

import de.ovgu.featureide.core.mpl.signature.ViewTag;

/** 
 * Abstract signature for class member.
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractSignature {
	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	protected static final int hashCodePrime = 31;
	public static final byte 
		VISIBILITY_DEFAULT = 0,
		VISIBILITY_PRIVATE = 1,
		VISIBILITY_PROTECTED = 2,
		VISIBILITY_PUBLIC = 3;
	
	protected boolean hasHashCode = false;
	protected int hashCode = 0;
	
	protected final AbstractClassSignature parent;
	
	protected final String name;
	protected final String[] modifiers;
	protected final String type;
	
	protected final boolean finalSignature;
	protected final byte visibility;
	
	protected String fullName;
	
//	protected final boolean ext;
	
	protected LinkedList<ViewTag> viewTags;
//	protected final HashSet<String> features = new HashSet<String>();
//	protected final FeatureList features = new FeatureList();
	
	protected int[] featureIDs;
	
	protected AbstractSignature(AbstractClassSignature parent, String name, String modifierString, String type) {
		this.parent = parent;
		this.name = name;
		if (parent != null) {
			this.fullName = parent.fullName + '.' + name;
		} else {
			this.fullName = '.' + name;
		}

//		this.viewTags = viewTags; 
		this.viewTags = null; 
//		this.ext = false;
		
		if (modifierString == null) {
			this.modifiers = new String[0];
		} else {
			this.modifiers = modifierString.trim().split(" ");
		}
		Arrays.sort(this.modifiers);
//		this.privateSignature = Arrays.binarySearch(this.modifiers, "private") >= 0;
		if (Arrays.binarySearch(this.modifiers, "private") >= 0) {
			this.visibility = VISIBILITY_PRIVATE;
		} else if (Arrays.binarySearch(this.modifiers, "protected") >= 0) {
			this.visibility = VISIBILITY_PROTECTED;
		} else if (Arrays.binarySearch(this.modifiers, "public") >= 0) {
			this.visibility = VISIBILITY_PUBLIC;
		} else {
			this.visibility = VISIBILITY_DEFAULT;
		}
		
		this.finalSignature = Arrays.binarySearch(this.modifiers, "final") >= 0;
		if (type == null) {
			this.type = "void";
		} else {
			this.type = type;
		}
	}
	
//	protected AbstractSignature(AbstractSignature orgSig, boolean ext) {
//		parent = orgSig.parent;
//		fullName = orgSig.fullName;
//		name = orgSig.name;
////				fullName.substring(fullName.lastIndexOf('.') + 1);
//		
//		viewTags = new LinkedList<ViewTag>(orgSig.viewTags); 
//		this.ext = orgSig.ext || ext;
//		
//		modifiers = new String[orgSig.modifiers.length];
//		System.arraycopy(orgSig.modifiers, 0, modifiers, 0, modifiers.length);
//
//		privateSignature =  orgSig.privateSignature;
//		finalSignature =  orgSig.finalSignature;
//		type =  orgSig.type;
//	}
	
//	public abstract AbstractSignature createExtendedSignature();
	
	protected void setFullName(String perfixName) {
		this.fullName = perfixName + '.' + name;
	}

	public AbstractClassSignature getParent() {
		return parent;
	}

	public boolean hasViewTags() {
		return viewTags != null;
	}
	
	public boolean hasViewTag(ViewTag viewTag) {
		if (viewTag == null) {
			return true;
		}
		if (viewTags != null) {
			for (ViewTag vt : viewTags) {
				if (vt.matches(viewTag)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public void addViewTag(ViewTag viewTag) {
		if (viewTags == null) {
			viewTags = new LinkedList<ViewTag>();
		}
		viewTags.add(viewTag);
	}
	
	public void clearViewTags() {
		viewTags = null;
	}
	
	public void deleteViewTag(String name) {
		if (viewTags != null) {
			Iterator<ViewTag> it = viewTags.iterator();
			while (it.hasNext()) {
				if (it.next().getName().equals(name)) {
					it.remove();
				}
			}
			if (viewTags.isEmpty()) {
				viewTags = null;
			}
		}
	}

	public LinkedList<ViewTag> getViewTags() {
		return viewTags;
	}

	public String getName() {
		return name;
	}
	
	public String getFullName() {
		return fullName;
	}
	
	public String[] getModifiers() {
		return modifiers;
	}
	
	public String getType() {
		return type;
	}
	
	public byte getVisibilty() {
		return visibility;
	}
	
	public boolean isPrivate() {
		return visibility == VISIBILITY_PRIVATE;
	}
	
	public boolean isProtected() {
		return visibility == VISIBILITY_PROTECTED;
	}
	
	public boolean isPublic() {
		return visibility == VISIBILITY_PUBLIC;
	}
	
	public boolean isDefault() {
		return visibility == VISIBILITY_DEFAULT;
	}
	
	public boolean isFinal() {
		return finalSignature;
	}

//	public boolean isExt() {
//		return ext;
//	}

//	public FeatureList getFeatures() {
//		return features;
//	}

	public int[] getFeatureIDs() {
		return featureIDs;
	}
	
	public void setFeatureIDs(int[] featureIDs) {
		this.featureIDs = featureIDs;
	}

//	public void addFeature(String feature) {
//		features.add(feature);
//	}
	
	public boolean hasFeature(int id) {
		for (int j = 0; j < featureIDs.length; j++) {
			if (id == featureIDs[j]) {
				return true;
			}
		}
		return false;
	}
	
	public boolean hasFeature(int[] idArray) {
		if (idArray == null) {
			return true;
		}
		for (int i = 0; i < idArray.length; i++) {
			int curId = idArray[i];
			for (int j = 0; j < featureIDs.length; j++) {
				if (curId == featureIDs[j]) {
					return true;
				}
			}
		}
		return false;
	}
	
//	public boolean hasFeature(List<String> featureList) {
//		if (featureList == null) {
//			return true;
//		}
//		for (String feature : featureList) {
//			if (features.contains(feature)) {
//				return true;
//			}
//		}
//		return false;
//	}
	
//	public HashSet<Integer> getFeatureIDs() {
//		return featureIDs;
//	}
//
//	public void addFeatureID(int id) {
//		featureIDs.add(id);
//	}

	@Override
	public final int hashCode() {
		if (!hasHashCode) {
			computeHashCode();
			hasHashCode = true;
		}
		return hashCode;
	}
	
	protected void computeHashCode() {
		hashCode = 1;
		hashCode = hashCodePrime * hashCode + fullName.hashCode();
		hashCode = hashCodePrime * hashCode + Arrays.hashCode(modifiers);
		hashCode = hashCodePrime * hashCode + type.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		
		return sigEquals((AbstractSignature) obj);
	}
	
	protected boolean sigEquals(AbstractSignature otherSig) {
		if (!fullName.equals(otherSig.fullName) 
//				|| !type.equals(otherSig.type) 
				|| !Arrays.equals(modifiers, otherSig.modifiers)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
//		sb.append(LINE_SEPARATOR);
//		sb.append("/* ext: ");
//		sb.append(ext);
//		sb.append(" */ ");
//		sb.append(LINE_SEPARATOR);
		if (hasViewTags()) {
			sb.append("//+ ");
			for (ViewTag viewTag : viewTags) {
				sb.append(viewTag.toString());
				sb.append(", ");
			}
			sb.delete(sb.length() - 2, sb.length());
		}
		return sb.toString();
	}
}
