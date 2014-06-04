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
package de.ovgu.featureide.core.mpl.signature.javadoc;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature.FeatureData;

/**
 * Abstract merger for modul-comment.
 * 
 * @author Sebastian Krieter
 */
public abstract class AJavaDocCommentMerger {
	public static int
		STAT_NUM_FEATURE0 = 0,
		STAT_NUM_GENERAL0 = 0,
		STAT_NUM_FEATURE1 = 0,
		STAT_NUM_GENERAL1 = 0,
		STAT_NUM_NEW = 0,
		STAT_BEFORE_CHARS = 0,
		STAT_AFTER_CHARS = 0,
		STAT_BEFORE_TAGS = 0,
		STAT_AFTER_TAGS = 0;
	
	public static void reset() {
		STAT_BEFORE_CHARS = 0;
		STAT_AFTER_CHARS = 0;
		STAT_BEFORE_TAGS = 0;
		STAT_AFTER_TAGS = 0;
		STAT_NUM_FEATURE0 = 0;
		STAT_NUM_GENERAL0 = 0;
		STAT_NUM_FEATURE1 = 0;
		STAT_NUM_GENERAL1 = 0;
		STAT_NUM_NEW = 0;
		}
	
	protected static final class Tag implements Comparable<Tag> {
		private final int tagtype, priority;
		private final String type;
		private String desc;

		public Tag(String type, String desc, int tagtype, int priority) {
			this.type = type;
			this.desc = desc;
			this.tagtype = tagtype;
			this.priority = priority;
		}
		
		@Override
		public int compareTo(Tag o) {
			int result = tagtype - o.tagtype;
			if (result != 0) {
				return result;
			} else {
				return type.compareTo(o.type);
			}
		}

		@Override
		public boolean equals(Object obj) {
			if (obj == null || !(obj instanceof Tag)) {
				return false;
			}
			Tag otherTag = (Tag)obj;
			return tagtype == otherTag.tagtype && type.equals((otherTag).type);
		}
		
		public int getPriority() {
			return priority;
		}

		public int getTagtype() {
			return tagtype;
		}
		
		public String getDesc() {
			return desc;
		}

		public void setDesc(String desc) {
			this.desc = desc;
		}

		@Override
		public int hashCode() {
			return type.hashCode();
		}

		@Override
		public String toString() {
			if (type.isEmpty()) {
				return desc;
			}
			return type + " " + desc;
		}
	}

	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	protected static final int 
		TAG_UNKNOWN = Integer.MAX_VALUE,
		TAG_DESCRIPTION = 0,
		TAG_AUTHOR = 1,
		TAG_VERSION = 2,
		TAG_PARAM = 3,
		TAG_RETURN = 4,
		TAG_THROWS = 5,
		TAG_SEE = 6,
		TAG_SINCE = 7,
		TAG_SERIAL = 8,
		TAG_SERIALFIELD = 9,
		TAG_DEPRECATED = 10,
		RULE_MERGE = 0,
		RULE_OVERRIDE = 1,
		RULE_DISCARD = 2;
	
	private static final String start = "/**", end = "*/";
	private static final Pattern 
		pTag = Pattern.compile("[^{]\\s*@\\w+\\s"),
		pType = Pattern.compile("\\A\\s*[{]\\s*@[a-z]+\\s*\\d*\\s*[}]"),
		pStar = Pattern.compile("\n\\s*[*]");
	
	protected final InterfaceProject interfaceProject;
	protected int tempFeatureID, tempInfoType;
	
	private final int[] featureList;
	private int tempPriority, maxGeneralPriority;
	private AbstractSignature sig = null;
	private List<Tag>
		generalTags = new ArrayList<Tag>(),
		featureTags = new ArrayList<Tag>();
	
	protected AJavaDocCommentMerger(InterfaceProject interfaceProject, int[] featureList) {
		this.featureList = featureList;
		this.interfaceProject = interfaceProject;
	}
	
	public final void mergeComments() {
		if (sig == null) {
			return;
		}
		FeatureData[] featureDataArray = sig.getFeatureData();
		
		for (int i = 0; i < featureList.length; i++) {
			tempFeatureID = featureList[i];
			for (int j = 0; j < featureDataArray.length; j++) {
				FeatureData featureData = featureDataArray[j];
				if (featureData.getId() == tempFeatureID) {
					String comment = featureData.getComment();
					if (comment != null) {
						int startIndex = 0;
						int endIndex = comment.indexOf(end);
						
						while (endIndex > -1) {
							parseTags(comment.substring(startIndex + start.length(), endIndex));
							startIndex = comment.indexOf(start, endIndex + end.length());
							endIndex = comment.indexOf(end, endIndex + end.length());
						}
					} 
					break;
				}
			}
		}
		
		if (featureTags.isEmpty() && generalTags.isEmpty()) {
			return;
		} else {
			Collections.sort(generalTags);
			Collections.sort(featureTags);
			
			final StringBuilder sb = new StringBuilder();
			sb.append(start);
			
			buildFinalComment(sb, generalTags, featureTags);

			sb.append(LINE_SEPARATOR);
			sb.append(' ');
			sb.append(end);
			sb.append(LINE_SEPARATOR);
			
			String mergedComment = sb.toString();
			System.out.println();
			sig.setMergedjavaDocComment(mergedComment);
			STAT_AFTER_CHARS += mergedComment.length() -
					( end.length() + LINE_SEPARATOR.length() + 1 +
					  start.length() + LINE_SEPARATOR.length());
		}		
	}
	
	public void setSig(AbstractSignature sig) {
		this.sig = sig;
		this.generalTags.clear();
		this.featureTags.clear();
		maxGeneralPriority = 0;
	}
	
	protected abstract void buildFinalComment(StringBuilder sb, List<Tag> generalTags, List<Tag> featureTags);

	protected abstract int getRuleForCommentPart(Tag tag);
	protected Tag handleCommentPart(Tag tag) {
		return tag;
	}
	
	private Tag categorize(String part1, String part2) {
		if (part1.equals("")) {
			if (part2.isEmpty()) {
				return null;
			}
			return new Tag(part1, part2, TAG_DESCRIPTION, tempPriority);
		} else if (part1.equals("@author")) {
			return new Tag(part1 + " " + part2, "", TAG_AUTHOR, tempPriority);
		} else if (part1.equals("@version")) {
			return new Tag(part1, part2, TAG_VERSION, tempPriority);
		} else if (part1.equals("@param")) {
			Pattern whiteSpace = Pattern.compile("\\s+");
			Matcher m = whiteSpace.matcher(part2);
			if (m.find()) {
				int index = m.start();
				if (index > -1) {
					return new Tag(part1 + " " + part2.substring(0, m.start()), part2.substring(m.end()), TAG_PARAM, tempPriority);
				} else {
					return new Tag(part1 + " " + part2, "", TAG_PARAM, tempPriority);
				}
			} else {
				return new Tag(part1 + " " + part2, "", TAG_PARAM, tempPriority);
			}
		} else if (part1.equals("@return")) {
			return new Tag(part1, part2, TAG_RETURN, tempPriority);
		} else if (part1.equals("@throws") || part1.equals("@exception")) {
//			int index = part2.indexOf(' ');
//			if (index > -1) {
//				return new Tag(part1 + " " + part2.substring(0, index), part2.substring(index + 1), TAG_THROWS, tempPriority);
//			} else {
//				return new Tag(part1 + " " + part2, "", TAG_THROWS, tempPriority);
//			}
			Pattern whiteSpace = Pattern.compile("\\s+");
			Matcher m = whiteSpace.matcher(part2);
			if (m.find()) {
				int index = m.start();
				if (index > -1) {
					return new Tag(part1 + " " + part2.substring(0, m.start()), part2.substring(m.end()), TAG_THROWS, tempPriority);
				} else {
					return new Tag(part1 + " " + part2, "", TAG_THROWS, tempPriority);
				}
			} else {
				return new Tag(part1 + " " + part2, "", TAG_THROWS, tempPriority);
			}
		} else if (part1.equals("@see")) {
			return new Tag(part1 + " " + part2, "", TAG_SEE, tempPriority);
		} else if (part1.equals("@since")) {
			return new Tag(part1, part2, TAG_SINCE, tempPriority);
		} else if (part1.equals("@deprecated")) {
			return new Tag(part1, part2, TAG_DEPRECATED, tempPriority);
		} else if (part1.equals("@serial") || part1.equals("@serialData")) {
			return new Tag(part1, part2, TAG_SERIAL, tempPriority);
		} else if (part1.equals("@serialField")) {
			int index = part2.indexOf(' ');
			if (index > -1) {
				int secondIndex = part2.indexOf(' ', index);
				if (secondIndex > -1) {
					return new Tag(part1 + " " + part2.substring(0, secondIndex), part2.substring(index + 1), TAG_SERIALFIELD, tempPriority);
				} else {
					return new Tag(part1 + " " + part2.substring(0, index), part2.substring(index + 1), TAG_SERIALFIELD, tempPriority);
				}
			} else {
				return new Tag(part1 + " " + part2, "", TAG_SERIALFIELD, tempPriority);
			}
		} else {
			return new Tag(part1, part2, TAG_UNKNOWN, tempPriority);
		}
	}
	
	private void addCommentPart(Tag newTag) {
		if (newTag == null) {
			return;
		}
		STAT_BEFORE_CHARS += newTag.toString().length() + LINE_SEPARATOR.length();
		STAT_BEFORE_TAGS++;
		newTag = handleCommentPart(newTag);
		if (newTag == null) {
			return;
		}
		
		final List<Tag> tags = (tempInfoType == 0) ? generalTags : featureTags;
		
		int i = 0;
		for (Tag tag : tags) {
			if (tag.equals(newTag)) {
				final int comp = tag.getPriority() - newTag.getPriority();
				if (comp < 0) {
					tags.set(i, newTag);
				} else if (comp == 0) {
					switch (getRuleForCommentPart(newTag)) {
					case RULE_MERGE:
						if (!tag.desc.isEmpty()) {
							tag.desc += "</br>" + newTag.desc;
						} else {
							tag.desc = newTag.desc;
						}
						break;
					case RULE_OVERRIDE: 
						tags.set(i, newTag);
						break;
					}
				}
				return;
			}
			++i;
		}
		tags.add(newTag);
	}
	
	private void parseTags(String comment) {		
		Matcher mc = pType.matcher(comment);
		if (mc.find()) {
			String x = comment.substring(comment.indexOf('@') + 1, mc.end() - 1);
			String[] parts = x.split("\\s+");
			String typeString = parts[0];
			
			// Type
			if (typeString.equals("general")) {
				tempInfoType = 0;
			} else if (typeString.equals("feature")) {
				tempInfoType = 1;
			} else if (typeString.equals("new")) {
				tempInfoType = 1;
				featureTags.clear();
				STAT_NUM_NEW++;
			} else {
				//warning?
				tempInfoType = 1;
			}
			
			// Priority
			if (parts.length == 2) {
				try {
					tempPriority = Integer.parseInt(parts[1]);
				} catch (NumberFormatException e) {
					//warning?
					tempPriority = 0;
				}
			} else {
				tempPriority = 0;
			}
			
			comment = comment.substring(mc.end());
		} else {
			tempInfoType = 0;
			tempPriority = 0;
		}
		
		if (tempInfoType == 0) {
			if (tempPriority == 0) {
				STAT_NUM_GENERAL0++;
			} else {
				STAT_NUM_GENERAL1++;
			}
		} else {
			if (tempPriority == 0) {
				STAT_NUM_FEATURE0++;
			} else {
				STAT_NUM_FEATURE1++;
			}
		}
		
		if (tempInfoType == 0) {
			if (maxGeneralPriority < tempPriority) {
				generalTags.clear();
				maxGeneralPriority = tempPriority;
			} else if (maxGeneralPriority > tempPriority) {
				return;
			}
		}
		
		comment = pStar.matcher(comment).replaceAll("\n");
		Matcher m = pTag.matcher(comment);
		
		int x, y, z;
		if (m.find()) {
			x = m.start();
			z = m.end();
			
			addCommentPart(categorize("", comment.substring(1, x + 1).trim()));
			
			while (m.find()) {
				y = m.start();
				addCommentPart(categorize(comment.substring(x + 1, z - 1).trim(), comment.substring(z, y + 1).trim()));
				x = y;
				z = m.end();
			}
			addCommentPart(categorize(comment.substring(x + 1, z - 1).trim(), comment.substring(z).trim()));
		} else {
			addCommentPart(categorize("", comment.trim()));
		}
	}
}
