/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.mpl.signature.documentation.base;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import de.ovgu.featureide.core.mpl.signature.documentation.BlockTag;

/**
 * Abstract merger for modul-comment.
 * 
 * @author Sebastian Krieter
 */
public abstract class ADocumentationCommentMerger {
	protected int[] featureIDs = null;

	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	protected static final int 
		RULE_MERGE = 0,
		RULE_OVERRIDE = 1,
		RULE_DISCARD = 2;
	
	protected abstract void buildFinalComment(StringBuilder sb, List<BlockTag> generalTags, List<BlockTag> featureTags);

	protected abstract int getRuleForCommentPart(BlockTag tag);
	
	protected BlockTag adaptBlockTag(BlockTag tag) {
		return tag;
	}

	public String mergeLists(List<BlockTag> generalTags, List<BlockTag> featureTags) {
		if (generalTags.isEmpty() && featureTags.isEmpty()) {
			return "";
		} else {
			Collections.sort(generalTags);
			Collections.sort(featureTags);
			
			final StringBuilder sb = new StringBuilder();
			sb.append(ADocumentationCommentParser.COMMENT_START);
			
			buildFinalComment(sb, generalTags, featureTags);

			sb.append(LINE_SEPARATOR);
			sb.append(' ');
			sb.append(ADocumentationCommentParser.COMMENT_END);
			sb.append(LINE_SEPARATOR);
			
			return sb.toString();
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
								oldTag.setDesc(newTag.getDesc() + ("</br>" + newTag.getDesc()));
							} else {
								oldTag.setDesc(newTag.getDesc());
							}
							break;
						case RULE_OVERRIDE: 
							tagSet.put(newTag, newTag);
							break;
						}
					}
				}
			}
		}
		return new ArrayList<BlockTag>(tagSet.values());
	}

	public int[] getFeatureIDs() {
		return featureIDs;
	}

	public void setFeatureIDs(int[] featureIDs) {
		this.featureIDs = featureIDs;
	}
	
}
