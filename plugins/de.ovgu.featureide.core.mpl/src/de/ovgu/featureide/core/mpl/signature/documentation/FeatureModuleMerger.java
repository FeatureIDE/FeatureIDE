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
package de.ovgu.featureide.core.mpl.signature.documentation;

import java.util.List;
import java.util.ListIterator;

import de.ovgu.featureide.core.mpl.signature.documentation.base.ADocumentationCommentMerger;

/**
 * Modul-Comment merger for feature modules.
 * 
 * @author Sebastian Krieter
 */
public class FeatureModuleMerger extends ADocumentationCommentMerger {
	private final int featureID;
	
	public FeatureModuleMerger(int featureID) {
		this.featureID = featureID;
	}

	@Override
	protected int getRuleForCommentPart(BlockTag tag) {
		switch(tag.getTagtype()){
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
	
	// TODO FeaturID richtig behandeln
	@Override
	protected void buildFinalComment(StringBuilder sb, List<BlockTag> generalTags, List<BlockTag> featureTags) {
		ListIterator<BlockTag> itg = generalTags.listIterator();
		ListIterator<BlockTag> itf = featureTags.listIterator();
		while(itg.hasNext() || itf.hasNext()) {
			sb.append(LINE_SEPARATOR);
			
			if (!itg.hasNext()) {
				BlockTag f = itf.next();
				sb.append(f);
			} else if (!itf.hasNext()) {
				sb.append(itg.next());
			} else {
				BlockTag g = itg.next();
				BlockTag f = itf.next();
				int comp = g.compareTo(f);
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
	}

	@Override
	protected BlockTag adaptBlockTag(BlockTag tag) {
		if (tag.getInformationType() == 0 || featureID == tag.getFeatureID()) {
			return tag;
		} else {
			return null;
		}
	}
}
