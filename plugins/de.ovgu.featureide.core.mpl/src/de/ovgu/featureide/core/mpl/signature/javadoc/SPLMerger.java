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

import java.util.List;
import java.util.ListIterator;

import de.ovgu.featureide.core.mpl.InterfaceProject;

/**
 * Modul-Comment merger for SPLs.
 * 
 * @author Sebastian Krieter
 */
public class SPLMerger extends AJavaDocCommentMerger {
	
	public SPLMerger(InterfaceProject interfaceProject, int[] featureList) {
		super(interfaceProject, featureList);
	}

	@Override
	protected int getRuleForCommentPart(Tag tag) {
		switch(tag.getTagtype()){
		case TAG_UNKNOWN:
			return RULE_OVERRIDE;
		case TAG_DESCRIPTION:
			return RULE_MERGE;
		case TAG_AUTHOR:
			return RULE_OVERRIDE;
		case TAG_VERSION: 
			return RULE_OVERRIDE;
		case TAG_PARAM:
			return RULE_MERGE;
		case TAG_RETURN:
			return RULE_MERGE;
		case TAG_THROWS: 
			return RULE_MERGE;
		case TAG_SEE: 
			return RULE_OVERRIDE;
		case TAG_SINCE: 
			return RULE_OVERRIDE;
		case TAG_DEPRECATED: 
			return RULE_OVERRIDE;
		default:
			return RULE_OVERRIDE;
		}
	}

	@Override
	protected void buildFinalComment(StringBuilder sb, List<Tag> generalTags, List<Tag> featureTags) {
		ListIterator<Tag> itg = generalTags.listIterator();
		ListIterator<Tag> itf = featureTags.listIterator();
		while(itg.hasNext() || itf.hasNext()) {
			sb.append(LINE_SEPARATOR);
			
			if (!itg.hasNext()) {
				Tag f = itf.next();
				if (f.getPriority() > 0) {
					sb.append(f);
				}
			} else if (!itf.hasNext()) {
				sb.append(itg.next());
			} else {
				Tag g = itg.next();
				Tag f = itf.next();
				if (f.getPriority() == 0) {
					sb.append(g);
				} else {
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
			STAT_AFTER_TAGS++;
		}
	}

	@Override
	protected Tag handleCommentPart(Tag tag) {
		if (tempInfoType == 1 && tag != null && tag.getTagtype() != TAG_SEE) {
			tag.setDesc("<b>[" + interfaceProject.getFeatureName(tempFeatureID) + "]</b> " + tag.getDesc());
		}
		return tag;
	}
}
