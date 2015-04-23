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
		this.tagTypeString = type;
		this.desc = desc;
		this.tagType = tagtype;
		this.priority = priority;
		this.featureID = featureID;
		this.featureNode = featureNode;
	}

	@Override
	public int compareTo(BlockTag o) {
		int result = tagType - o.tagType;
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
		return tagType == otherTag.tagType && tagTypeString.equals((otherTag).tagTypeString);
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

	public Node getConstraint() {
		return featureNode;
	}
	
}
