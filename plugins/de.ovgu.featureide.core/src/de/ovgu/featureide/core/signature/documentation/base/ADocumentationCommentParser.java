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
package de.ovgu.featureide.core.signature.documentation.base;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.ovgu.featureide.core.signature.documentation.base.SignatureCommentPair.Comment;

/**
 * Abstract merger for modul-comment.
 * 
 * @author Sebastian Krieter
 */
public abstract class ADocumentationCommentParser {
	
	static final String COMMENT_START = "/**", COMMENT_END = "*/";
	private static final Pattern 
		pBlockTag = Pattern.compile("[^{]\\s*@\\w+\\s"),
		pCommentType = Pattern.compile("\\A\\s*[{]\\s*@[a-z]+\\s*\\d*\\s*[}]"),
		pStar = Pattern.compile("\n\\s*[*]");
	
	protected int curFeatureID, tagFeatureID, curPriority;
	
	protected final List<BlockTag>
		generalTags = new ArrayList<BlockTag>(),
		featureTags = new LinkedList<BlockTag>();
	
	protected BlockTag handleCommentPart(BlockTag tag) {
		return tag;
	}
	
	public void parse(List<Comment> comments) {
		for (Comment comment : comments) {
			final String commentString = comment.getComment();
			curFeatureID = comment.getFeatureID();
			
			int startIndex = 0;
			int endIndex = commentString.indexOf(COMMENT_END);
			
			while (endIndex > -1) {
				parseTags(commentString.substring(startIndex + COMMENT_START.length(), endIndex));
				startIndex = commentString.indexOf(COMMENT_START, endIndex + COMMENT_END.length());
				endIndex = commentString.indexOf(COMMENT_END, endIndex + COMMENT_END.length());
			}
		}					
	}
	
	protected abstract void parseHead(String[] parts);
	
	private void parseTags(String comment) {
		Matcher mc = pCommentType.matcher(comment);
		if (mc.find()) {
			parseHead(comment.substring(comment.indexOf('@') + 1, mc.end() - 1).split("\\s+"));
			comment = comment.substring(mc.end());
		} else {
			tagFeatureID = -1;
			curPriority = 0;
		}

		addBlockTagToList(comment);
	}

	private void addBlockTagToList(String comment) {
		final List<BlockTag> tagList = (tagFeatureID > -1) ? featureTags : generalTags;
		
		comment = pStar.matcher(comment).replaceAll("\n");
		Matcher m = pBlockTag.matcher(comment);
		
		int x, y, z;
		if (m.find()) {
			x = m.start();
			z = m.end();
			
			tagList.add(categorize("", comment.substring(1, x + 1).trim()));
			
			while (m.find()) {
				y = m.start();
				tagList.add(categorize(comment.substring(x + 1, z - 1).trim(), comment.substring(z, y + 1).trim()));
				x = y;
				z = m.end();
			}
			tagList.add(categorize(comment.substring(x + 1, z - 1).trim(), comment.substring(z).trim()));
		} else {
			tagList.add(categorize("", comment.trim()));
		}
	}
	
	private BlockTag categorize(String head, String body) {
		final BlockTag tag = BlockTag.construct(head, body);
		tag.setPriority(curPriority);
		tag.setFeatureID(tagFeatureID);
		return tag;
	}
	
	public List<BlockTag> getGeneralTags() {
		return generalTags;
	}
	
	public List<BlockTag> getFeatureTags() {
		return featureTags;
	}
	
}
