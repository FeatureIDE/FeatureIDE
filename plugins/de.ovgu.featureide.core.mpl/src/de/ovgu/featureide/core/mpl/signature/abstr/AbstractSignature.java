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

import java.util.HashSet;
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
	
	protected boolean hasHashCode = false;
	protected int hashCode = 0;
	
	protected final AbstractClassSignature parent;
	
	protected final String name;
	protected final String modifiers;
	protected final String type;
	protected final boolean privateSignature;
	
	protected String fullName;
	
	protected final boolean ext;
	
	protected LinkedList<ViewTag> viewTags;
	protected HashSet<String> features = new HashSet<String>();
	
	protected AbstractSignature(AbstractClassSignature parent, String name, String modifiers, String type, LinkedList<ViewTag> viewTags) {
		this.parent = parent;
		this.name = name;
		if (parent != null) {
			this.fullName = parent.fullName + '.' + name;
		} else {
			this.fullName = '.' + name;
		}
		
		this.viewTags = viewTags; 
		this.ext = false;
		
		if (modifiers == null) {
			this.modifiers = "";
		} else {
			this.modifiers = modifiers.trim();
		}
		this.privateSignature = this.modifiers.contains("private");
		if (type == null) {
			this.type = "";
		} else {
			this.type = type;
		}
	}
	
	protected AbstractSignature(AbstractSignature orgSig, boolean ext) {
		parent = orgSig.parent;
		fullName = orgSig.fullName;
		name = orgSig.name;
//				fullName.substring(fullName.lastIndexOf('.') + 1);
		
		viewTags = new LinkedList<ViewTag>(orgSig.viewTags); 
		this.ext = orgSig.ext || ext;
		
		modifiers =  orgSig.modifiers;
		privateSignature =  orgSig.privateSignature;
		type =  orgSig.type;
	}
	
	public abstract AbstractSignature createExtendedSignature();
	
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
	
	public String getModifiers() {
		return modifiers;
	}
	
	public String getType() {
		return type;
	}
	
	public boolean isPrivate() {
		return privateSignature;
	}

	public boolean isExt() {
		return ext;
	}

	public HashSet<String> getFeatures() {
		return features;
	}

	public void addFeature(String feature) {
		features.add(feature);
	}

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
		hashCode = hashCodePrime * hashCode + modifiers.hashCode();
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
		if (!type.equals(otherSig.type) 
				|| !fullName.equals(otherSig.fullName) 
				|| !modifiers.equals(otherSig.modifiers)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(LINE_SEPARATOR);
		sb.append("/* ext: ");
		sb.append(ext);
		sb.append(" */ ");
		sb.append(LINE_SEPARATOR);
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
