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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

import de.ovgu.featureide.fm.core.filter.base.Filter;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

/**
 * Abstract merger for modul-comment.
 *
 * @author Sebastian Krieter
 */
public abstract class ADocumentationCommentMerger implements Comparator<BlockTag>, Serializable {

	private static final long serialVersionUID = 1L;

	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	protected static final int RULE_MERGE = 0, RULE_OVERRIDE = 1, RULE_DISCARD = 2;

	private final List<IFilter<?>> filterList = new LinkedList<>();

	protected int[] featureIDRanks = null;

	public void setValidFeatureIDs(int numberOfFeatures, int[] validFeatureIDs) {
		featureIDRanks = new int[numberOfFeatures];
		for (int i = 0; i < featureIDRanks.length; i++) {
			featureIDRanks[i] = -1;
			for (int j = 0; j < validFeatureIDs.length; j++) {
				if (validFeatureIDs[j] == i) {
					featureIDRanks[i] = j;
					break;
				}
			}
		}
	}

	public String merge(List<BlockTag> generalTags, List<BlockTag> featureTags) {
//		Filter.filter(generalTags, filterList);
		Filter.filter(featureTags, filterList);

		sortFeatureList(featureTags);

		featureTags = mergeList(featureTags);
		generalTags = mergeList(generalTags);

		return mergeLists(generalTags, featureTags);
	}

	public String mergeLists(List<BlockTag> generalTags, List<BlockTag> featureTags) {
		if (generalTags.isEmpty() && featureTags.isEmpty()) {
			return "";
		} else {
			Collections.sort(generalTags);
			Collections.sort(featureTags);

			final StringBuilder sb = new StringBuilder();
			sb.append(ADocumentationCommentParser.COMMENT_START);

			final ListIterator<BlockTag> itg = generalTags.listIterator();
			final ListIterator<BlockTag> itf = featureTags.listIterator();

			while (itg.hasNext() || itf.hasNext()) {
				sb.append(LINE_SEPARATOR);

				if (!itg.hasNext()) {
					sb.append(itf.next());
				} else if (!itf.hasNext()) {
					sb.append(itg.next());
				} else {
					final BlockTag g = itg.next();
					final BlockTag f = itf.next();
					final int comp = g.compareTo(f);
					if (comp < 0) {
						sb.append(g);
						itf.previous();
					} else if (comp == 0) {
						sb.append(g);
						sb.append("</br>");
						sb.append(f.getDesc());
					} else {
						sb.append(f);
						itg.previous();
					}
				}
			}

			sb.append(LINE_SEPARATOR);
			sb.append(' ');
			sb.append(ADocumentationCommentParser.COMMENT_END);
			sb.append(LINE_SEPARATOR);

			return sb.toString();
		}
	}

	public void sortFeatureList(List<BlockTag> tagList) {
		if (featureIDRanks != null) {
			for (final Iterator<BlockTag> it = tagList.iterator(); it.hasNext();) {
				final BlockTag tag = it.next();
				if ((tag.getFeatureID() > -1) && (featureIDRanks[tag.getFeatureID()] == -1)) {
					it.remove();
				}
			}
			Collections.sort(tagList, this);
		}
	}

	public List<BlockTag> mergeList(List<BlockTag> tagList) {
		final HashMap<BlockTag, BlockTag> tagSet = new HashMap<>();

		for (BlockTag newTag : tagList) {
			newTag = adaptBlockTag(newTag);
			if (newTag != null) {
				final BlockTag oldTag = tagSet.get(newTag);
				if (oldTag == null) {
					tagSet.put(newTag, newTag);
				} else {
					final int comp = oldTag.getPriority() - newTag.getPriority();
					if (comp < 0) {
						tagSet.put(newTag, newTag);
					} else if (comp == 0) {
						switch (getRuleForCommentPart(newTag)) {
						case RULE_MERGE:
							if (!oldTag.getDesc().isEmpty()) {
								oldTag.setDesc(oldTag.getDesc() + ("</br>" + newTag.getDesc()));
							} else {
								oldTag.setDesc(newTag.getDesc());
							}
							break;
						case RULE_OVERRIDE:
							tagSet.put(newTag, newTag);
							break;
						case RULE_DISCARD:
						default:
							break;
						}
					}
				}
			}
		}
		return new ArrayList<BlockTag>(tagSet.values());
	}

	protected BlockTag adaptBlockTag(BlockTag tag) {
		return tag;
	}

	protected int getRuleForCommentPart(BlockTag tag) {
		switch (tag.getTagtype()) {
		case BlockTag.TAG_UNKNOWN:
			return RULE_OVERRIDE;
		case BlockTag.TAG_DESCRIPTION:
			return RULE_MERGE;
		case BlockTag.TAG_AUTHOR:
			return RULE_OVERRIDE;
		case BlockTag.TAG_VERSION:
			return RULE_OVERRIDE;
		case BlockTag.TAG_PARAM:
			return RULE_MERGE;
		case BlockTag.TAG_RETURN:
			return RULE_MERGE;
		case BlockTag.TAG_THROWS:
			return RULE_MERGE;
		case BlockTag.TAG_SEE:
			return RULE_OVERRIDE;
		case BlockTag.TAG_SINCE:
			return RULE_OVERRIDE;
		case BlockTag.TAG_DEPRECATED:
			return RULE_OVERRIDE;
		default:
			return RULE_OVERRIDE;
		}
	}

	@Override
	public int compare(BlockTag tag1, BlockTag tag2) {
		if ((tag1.getFeatureID() == -1) || (tag2.getFeatureID() == -1)) {
			return 0;
		}
		return featureIDRanks[tag1.getFeatureID()] - featureIDRanks[tag2.getFeatureID()];
	}

	public void addFilter(IFilter<?> filter) {
		filterList.add(filter);
	}

}
