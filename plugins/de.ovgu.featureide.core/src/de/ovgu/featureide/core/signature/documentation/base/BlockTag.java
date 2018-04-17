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
package de.ovgu.featureide.core.signature.documentation.base;

import org.prop4j.Node;

import de.ovgu.featureide.core.signature.base.IConstrainedObject;

public class BlockTag implements Comparable<BlockTag>, IConstrainedObject {

	public static final int TAG_UNKNOWN = Integer.MAX_VALUE, TAG_DESCRIPTION = 0, TAG_AUTHOR = 1, TAG_VERSION = 2, TAG_PARAM = 3, TAG_RETURN = 4,
			TAG_THROWS = 5, TAG_SEE = 6, TAG_SINCE = 7, TAG_SERIAL = 8, TAG_SERIALFIELD = 9, TAG_DEPRECATED = 10;

	private final int tagType, priority, featureID;
	private final String tagTypeString;
	private final Node featureNode;

	private String desc;

	BlockTag(String type, String desc, int tagtype, int priority, int featureID, Node featureNode) {
		tagTypeString = type;
		this.desc = desc;
		tagType = tagtype;
		this.priority = priority;
		this.featureID = featureID;
		this.featureNode = featureNode;
	}

	@Override
	public int compareTo(BlockTag o) {
		final int result = tagType - o.tagType;
		if (result != 0) {
			return result;
		} else {
			return tagTypeString.compareTo(o.tagTypeString);
		}
	}

	@Override
	public boolean equals(Object obj) {
		if (!(obj instanceof BlockTag)) {
			return false;
		}
		final BlockTag otherTag = (BlockTag) obj;
		return (tagType == otherTag.tagType) && tagTypeString.equals((otherTag).tagTypeString);
	}

	public int getPriority() {
		return priority;
	}

	public int getTagtype() {
		return tagType;
	}

	public String getDesc() {
		return desc;
	}

	public void setDesc(String desc) {
		this.desc = desc;
	}

	@Override
	public int hashCode() {
		return tagTypeString.hashCode();
	}

	@Override
	public String toString() {
		if (tagTypeString.isEmpty()) {
			return desc;
		}
		return tagTypeString + " " + desc;
	}

	public int getFeatureID() {
		return featureID;
	}

	public boolean isFeatureSpecific() {
		return featureNode != null;
	}

	public boolean isFeatureIndependent() {
		return !isFeatureSpecific();
	}

	@Override
	public Node getConstraint() {
		return featureNode;
	}

}
