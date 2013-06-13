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

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Abstract signature for one class.
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractClassFragment {
	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	protected static final int hashCodePrime = 31;
	
	protected boolean hasHashCode = false;
	protected int hashCode = 0;
	
	protected final AbstractClassSignature signature;

	protected Collection<AbstractSignature> members;
	protected Map<AbstractClassSignature, AbstractClassFragment> innerClasses;
	
	protected AbstractClassFragment(AbstractClassSignature signature) {
		this.signature = signature;
	}

	public AbstractClassSignature getSignature() {
		return signature;
	}
	
	public Collection<AbstractSignature> getMembers() {
		return members;
	}
	
	public Map<AbstractClassSignature, AbstractClassFragment> getInnerClasses() {
		return innerClasses;
	}
	
	public AbstractClassFragment getInnerClass(AbstractClassSignature classSignature) {
		return innerClasses.get(classSignature);
	}
	
	public int getMemberCount() {
		int innerMembers = 0;
		for (AbstractClassFragment innerClass : innerClasses.values()) {
			innerMembers += innerClass.getMemberCount();
		}
		return members.size() + innerClasses.size()	+ innerMembers;
	}
	
	public void addMember(AbstractSignature member) {
		members.add(member);
		hasHashCode = false;
	}

	public void addInnerClass(AbstractClassFragment innerClass) {
		AbstractClassFragment orgInnerClass = innerClasses.get(innerClass.getSignature());
		if (orgInnerClass == null) {
			innerClasses.put(innerClass.getSignature(), innerClass);
		} else {
			for (AbstractSignature member : innerClass.members) {
				orgInnerClass.addMember(member);
			}
			for (AbstractClassFragment innerInnerClass : innerClass.innerClasses.values()) {
				orgInnerClass.addInnerClass(innerInnerClass);
			}
		}
		hasHashCode = false;
	}
	
	public abstract String toString();
	public abstract String toShortString();

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
		hashCode = hashCodePrime * hashCode + signature.hashCode();

		hashCode *= hashCodePrime;
		for (AbstractSignature member : members) {
			hashCode += member.hashCode();
		}
		
		hashCode *= hashCodePrime;
		for (AbstractClassFragment innerClass : innerClasses.values()) {
			hashCode += innerClass.hashCode();
		}
	}

	@Override
	public final boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || getClass() != obj.getClass())
			return false;
		
		AbstractClassFragment other = (AbstractClassFragment) obj;
		
		if (members.size() != other.members.size()
				|| innerClasses.size() != other.innerClasses.size()
				|| !signature.equals(other.signature)) {
			return false;
		}
		for (AbstractSignature member : members) {
			if (!other.members.contains(member)) {
				return false;
			}
		}
		for (Entry<AbstractClassSignature, AbstractClassFragment> entry : innerClasses.entrySet()) {
			AbstractClassFragment otherClassFragment = other.innerClasses.get(entry.getKey());
			if (otherClassFragment == null
					|| !otherClassFragment.equals(entry.getValue())) {
				return false;
			}
		}
		return true;
	}
}
