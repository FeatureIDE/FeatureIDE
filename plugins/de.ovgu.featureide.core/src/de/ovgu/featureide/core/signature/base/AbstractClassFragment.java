/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.signature.base;

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
	protected int hashCode = 0, nonPrivateMemberCount = 0, nonPrivateInnerClassCount = 0;

	protected final AbstractClassSignature signature;

	protected Collection<AbstractSignature> members;
	protected Map<String, AbstractClassFragment> innerClasses;

	protected AbstractClassFragment(AbstractClassSignature signature) {
		this.signature = signature;
	}

	public AbstractClassSignature getSignature() {
		return signature;
	}

	public Collection<AbstractSignature> getMembers() {
		return members;
	}

	public Map<String, AbstractClassFragment> getInnerClasses() {
		return innerClasses;
	}

	public AbstractClassFragment getInnerClass(String classSignatureName) {
		return innerClasses.get(classSignatureName);
	}

	public int getMemberCount() {
		int innerMembers = 0;
		for (final AbstractClassFragment innerClass : innerClasses.values()) {
			innerMembers += innerClass.getMemberCount();
		}
		return members.size() + innerClasses.size() + innerMembers;
	}

	public int getNonPrivateMemberCount() {
		return nonPrivateMemberCount;
	}

	public int getNonPrivateInnerClassCount() {
		return nonPrivateInnerClassCount;
	}

	public void addMember(AbstractSignature member) {
		members.add(member);
		if (!member.isPrivate()) {
			nonPrivateMemberCount++;
			hasHashCode = false;
		}
	}

	public void addInnerClass(AbstractClassFragment innerClass) {
		final AbstractClassFragment orgInnerClass = innerClasses.get(innerClass.getSignature().getFullName());
		if (orgInnerClass == null) {
			innerClasses.put(innerClass.getSignature().getFullName(), innerClass);
			if (!innerClass.getSignature().isPrivate()) {
				nonPrivateInnerClassCount++;
			}
		} else {
			for (final AbstractSignature member : innerClass.members) {
				orgInnerClass.addMember(member);
			}
			for (final AbstractClassFragment innerInnerClass : innerClass.innerClasses.values()) {
				orgInnerClass.addInnerClass(innerInnerClass);
			}
		}
		hasHashCode = false;
	}

	@Override
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
		hashCode = hashCodePrime + signature.hashCode();

		hashCode *= hashCodePrime;
		for (final AbstractSignature member : members) {
			if (!member.isPrivate()) {
				hashCode += member.hashCode();
			}
		}

		hashCode *= hashCodePrime;
		for (final AbstractClassFragment innerClass : innerClasses.values()) {
			if (!innerClass.getSignature().isPrivate()) {
				hashCode += innerClass.hashCode();
			}
		}
	}

	@Override
	public final boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}

		final AbstractClassFragment other = (AbstractClassFragment) obj;

		if ((nonPrivateMemberCount != other.nonPrivateMemberCount) || (nonPrivateInnerClassCount != other.nonPrivateInnerClassCount)
			|| !signature.equals(other.signature)) {
			return false;
		}
		for (final AbstractSignature member : members) {
			if (!member.isPrivate() && !other.members.contains(member)) {
				return false;
			}
		}
		for (final Entry<String, AbstractClassFragment> entry : innerClasses.entrySet()) {
			if (!entry.getValue().getSignature().isPrivate()) {
				final AbstractClassFragment otherClassFragment = other.innerClasses.get(entry.getKey());
				if ((otherClassFragment == null) || !otherClassFragment.equals(entry.getValue())) {
					return false;
				}
			}
		}
		return true;
	}
}
