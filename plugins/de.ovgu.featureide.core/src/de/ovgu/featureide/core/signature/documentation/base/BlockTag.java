package de.ovgu.featureide.core.signature.documentation.base;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class BlockTag implements Comparable<BlockTag> {
	public static final int TAG_UNKNOWN = Integer.MAX_VALUE, TAG_DESCRIPTION = 0, TAG_AUTHOR = 1, TAG_VERSION = 2, TAG_PARAM = 3, TAG_RETURN = 4,
			TAG_THROWS = 5, TAG_SEE = 6, TAG_SINCE = 7, TAG_SERIAL = 8, TAG_SERIALFIELD = 9, TAG_DEPRECATED = 10;

	private final int tagType;
	private final String tagTypeString;

	private int priority;
	private String desc;
	
	private int featureID;

	public static BlockTag construct(String head, String body) {
		switch (head) {
		case "":
			if (body.isEmpty()) {
				return null;
			}
			return new BlockTag(head, body, TAG_DESCRIPTION);
		case "@author":
			return new BlockTag(head + " " + body, "", TAG_AUTHOR);
		case "@version":
			return new BlockTag(head, body, TAG_VERSION);
		case "@param": {
			final Pattern whiteSpace = Pattern.compile("\\s+");
			final Matcher m = whiteSpace.matcher(body);
			if (m.find()) {
				int index = m.start();
				if (index > -1) {
					return new BlockTag(head + " " + body.substring(0, m.start()), body.substring(m.end()), TAG_PARAM);
				} else {
					return new BlockTag(head + " " + body, "", TAG_PARAM);
				}
			} else {
				return new BlockTag(head + " " + body, "", TAG_PARAM);
			}
		}
		case "@return":
			return new BlockTag(head, body, TAG_RETURN);
		case "@throws":
		case "@exception": {
			final Pattern whiteSpace = Pattern.compile("\\s+");
			final Matcher m = whiteSpace.matcher(body);
			if (m.find()) {
				int index = m.start();
				if (index > -1) {
					return new BlockTag(head + " " + body.substring(0, m.start()), body.substring(m.end()), TAG_THROWS);
				} else {
					return new BlockTag(head + " " + body, "", TAG_THROWS);
				}
			} else {
				return new BlockTag(head + " " + body, "", TAG_THROWS);
			}
		}
		case "@see":
			return new BlockTag(head + " " + body, "", TAG_SEE);
		case "@since":
			return new BlockTag(head, body, TAG_SINCE);
		case "@deprecated":
			return new BlockTag(head, body, TAG_DEPRECATED);
		case "@serial":
		case "@serialData":
			return new BlockTag(head, body, TAG_SERIAL);
		case "@serialField":
			int index = body.indexOf(' ');
			if (index > -1) {
				int secondIndex = body.indexOf(' ', index);
				if (secondIndex > -1) {
					return new BlockTag(head + " " + body.substring(0, secondIndex), body.substring(secondIndex + 1), TAG_SERIALFIELD);
				} else {
					return new BlockTag(head + " " + body.substring(0, index), body.substring(index + 1), TAG_SERIALFIELD);
				}
			} else {
				return new BlockTag(head + " " + body, "", TAG_SERIALFIELD);
			}
		default:
			return construct(head, body, 0, TAG_UNKNOWN);
		}
	}
	
	private static BlockTag construct(String head, String body, int keyParts, int type) {
		switch (keyParts) {
		case 0:
			return new BlockTag(head, body, type);
		case Integer.MAX_VALUE:
			return new BlockTag(head + " " + body, "", type);
		default:
			final Pattern whiteSpace = Pattern.compile("\\s+");
			final Matcher m = whiteSpace.matcher(body);
			
			int countParts = 0, startIndex = -1, endIndex = 0;
			while (m.find() && (countParts++ < keyParts)) {
				startIndex = m.start();
				endIndex = m.end();
			}
			return (startIndex > -1) 
				? new BlockTag(head + " " + body.substring(0, startIndex), body.substring(endIndex), type) 
				: new BlockTag(head + " " + body, "", type);
		}
	}

	public BlockTag(String type, String desc, int tagtype, int priority) {
		this.tagTypeString = type;
		this.desc = desc;
		this.tagType = tagtype;
		this.priority = priority;
	}

	public BlockTag(String type, String desc, int tagtype) {
		this.tagTypeString = type;
		this.desc = desc;
		this.tagType = tagtype;
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

	public void setPriority(int priority) {
		this.priority = priority;
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

	public void setFeatureID(int featureID) {
		this.featureID = featureID;
	}

	public boolean isFeatureSpecific() {
		return featureID > -1;
	}
	
	public boolean isFeatureIndependent() {
		return !isFeatureSpecific();
	}
}
