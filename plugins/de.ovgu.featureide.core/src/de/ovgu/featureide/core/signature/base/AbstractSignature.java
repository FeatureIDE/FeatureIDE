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

import java.util.Arrays;

import org.prop4j.Node;
import org.prop4j.Or;

/**
 * Abstract signature for a class member.
 *
 * @author Sebastian Krieter
 */
public abstract class AbstractSignature implements IConstrainedObject {

	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	protected static final int hashCodePrime = 31;
	public static final byte VISIBILITY_DEFAULT = 0, VISIBILITY_PRIVATE = 1, VISIBILITY_PROTECTED = 2, VISIBILITY_PUBLIC = 3;

	protected boolean hasHashCode = false;
	protected int hashCode = 0;

	protected final AbstractClassSignature parent;

	protected final String name;
	protected final String[] modifiers;
	protected final String type;

	protected final boolean finalSignature;
	protected final byte visibility;

	protected String fullName;

	protected AFeatureData[] featureData = null;
	protected String mergedjavaDocComment = null;

	protected int startLine = -1;
	protected int endLine = -1;

	protected AbstractSignature(AbstractClassSignature parent, String name, String modifierString, String type) {
		this.parent = parent;
		this.name = name;
		if (parent != null) {
			fullName = parent.fullName + '.' + name;
		} else {
			fullName = '.' + name;
		}

		if (modifierString == null) {
			modifiers = new String[0];
		} else {
			modifiers = modifierString.trim().split("\\s+");
		}
		Arrays.sort(modifiers);
		if (Arrays.binarySearch(modifiers, "private") >= 0) {
			visibility = VISIBILITY_PRIVATE;
		} else if (Arrays.binarySearch(modifiers, "protected") >= 0) {
			visibility = VISIBILITY_PROTECTED;
		} else if (Arrays.binarySearch(modifiers, "public") >= 0) {
			visibility = VISIBILITY_PUBLIC;
		} else {
			visibility = VISIBILITY_DEFAULT;
		}

		finalSignature = Arrays.binarySearch(modifiers, "final") >= 0;
		if (type == null) {
			this.type = "void";
		} else {
			this.type = type;
		}
	}

	protected AbstractSignature(AbstractClassSignature parent, String name, String modifierString, String type, int startLine, int endLine) {
		this(parent, name, modifierString, type);
		this.startLine = startLine;
		this.endLine = endLine;
	}

	public int getStartLine() {
		return startLine;
	}

	public void setStartLine(int startLine) {
		this.startLine = startLine;
	}

	public int getEndLine() {
		return endLine;
	}

	public void setEndLine(int endLine) {
		this.endLine = endLine;
	}

	protected void setFullName(String perfixName) {
		fullName = perfixName + '.' + name;
	}

	public AbstractClassSignature getParent() {
		return parent;
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

	public String getMergedjavaDocComment() {
		return mergedjavaDocComment;
	}

	public AFeatureData[] getFeatureData() {
		return featureData;
	}

	public AFeatureData getFirstFeatureData() {
		return ((featureData == null) || (featureData.length == 0)) ? null : featureData[0];
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

	public void setMergedjavaDocComment(String mergedjavaDocComment) {
		this.mergedjavaDocComment = mergedjavaDocComment;
	}

	public void setFeatureData(AFeatureData[] featureData) {
		if (this.featureData == null) {
			this.featureData = featureData;
		}
	}

	public void setFeatureData(AFeatureData featureData) {
		if (this.featureData == null) {
			this.featureData = new AFeatureData[] { featureData };
		}
	}

	public int hasFeature(int id) {
		if (featureData != null) {
			for (int j = 0; j < featureData.length; j++) {
				if (featureData[j].hasID(id)) {
					return j;
				}
			}
		}
		return -1;
	}

	public boolean hasFeature(int[] idArray) {
		if (idArray == null) {
			return true;
		}
		if (featureData != null) {
			for (int j = 0; j < featureData.length; j++) {
				final AFeatureData curFeatureData = featureData[j];
				for (int i = 0; i < idArray.length; i++) {
					if (curFeatureData.hasID(idArray[i])) {
						return true;
					}
				}
			}
		}
		return false;
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
		hashCode = (hashCodePrime * hashCode) + fullName.hashCode();
//		hashCode = hashCodePrime * hashCode + type.hashCode();
//		hashCode = hashCodePrime * hashCode + Arrays.hashCode(modifiers);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}

		return sigEquals((AbstractSignature) obj);
	}

	protected boolean sigEquals(AbstractSignature otherSig) {
		if (!fullName.equals(otherSig.fullName)
//				|| !type.equals(otherSig.type)
//				|| !Arrays.equals(modifiers, otherSig.modifiers)
		) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return fullName + " : " + type;
	}

	@Override
	public Node getConstraint() {
		if (featureData == null) {
			return null;
		}

		final Node[] constraints = new Node[featureData.length];
		for (int i = 0; i < constraints.length; i++) {
			final Node constraint = featureData[i].getConstraint();
			if (constraint == null) {
				return null;
			}
			constraints[i] = constraint.clone();
		}

		return new Or(constraints).toCNF();
	}
}
