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

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.core.builder.IComposerObject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.documentation.base.SignatureCommentPair.Comment;

/**
 * Abstract merger for module-comment.
 *
 * @author Sebastian Krieter
 */
public abstract class ADocumentationCommentParser implements IComposerObject {

	static final String COMMENT_START = "/**", COMMENT_END = "*/";

	private static final Pattern pStart = Pattern.compile("\\/\\*\\*[\\*\n\\s]*"),
			pCommentType = Pattern.compile("\\A\\s*[{]\\s*@(feature|general|new)(\\s+(\\w)+)*\\s*[}]"), pBlockTag = Pattern.compile("[^{]\\s*@\\w+\\s"),
			pStar = Pattern.compile("\n\\s*[*]");

	protected final List<BlockTag> generalTags = new ArrayList<BlockTag>(), featureTags = new LinkedList<BlockTag>();

	protected int curFeatureID, tagPriority;
	protected Node tagFeatureNode;

	private BlockTagConstructor tagConstructor;

	public final void parse(ProjectSignatures projectSignatures, List<Comment> comments) {
		tagConstructor = new BlockTagConstructor(projectSignatures);
		generalTags.clear();
		featureTags.clear();

		for (final Comment comment : comments) {
			final String commentString = comment.getComment();
			curFeatureID = comment.getFeatureID();

			final Matcher startMatcher = pStart.matcher(commentString);
			while (startMatcher.find()) {
				parseTags(commentString.substring(startMatcher.end(), commentString.indexOf(COMMENT_END, startMatcher.start())));
			}
		}
	}

	protected final Node getCurFeatureNode() {
		return new Literal(tagConstructor.getProjectSignatures().getFeatureName(curFeatureID));
	}

	protected final Node getCurFeatureNode(int featureID) {
		return new Literal(tagConstructor.getProjectSignatures().getFeatureName(featureID));
	}

	protected abstract void parseHead(String[] parts);

	protected BlockTag handleCommentPart(BlockTag tag) {
		return tag;
	}

	private void parseTags(String comment) {
		final Matcher mc = pCommentType.matcher(comment);
		if (mc.find()) {
			parseHead(comment.substring(comment.indexOf('@') + 1, mc.end() - 1).split("\\s+"));
			comment = comment.substring(mc.end());
		} else {
			tagFeatureNode = null;
			tagPriority = 0;
		}

		addBlockTagToList(comment);
	}

	private void addBlockTagToList(String comment) {
		final List<BlockTag> tagList = (tagFeatureNode != null) ? featureTags : generalTags;

		comment = pStar.matcher(comment).replaceAll("\n");
		final Matcher m = pBlockTag.matcher(comment);

		int x, y, z;
		if (m.find()) {
			x = m.start();
			z = m.end();

			categorize(tagList, "", comment.substring(0, x + 1).trim());

			while (m.find()) {
				y = m.start();
				categorize(tagList, comment.substring(x + 1, z - 1).trim(), comment.substring(z, y + 1).trim());
				x = y;
				z = m.end();
			}
			categorize(tagList, comment.substring(x + 1, z - 1).trim(), comment.substring(z).trim());
		} else {
			categorize(tagList, "", comment.trim());
		}
	}

	private void categorize(List<BlockTag> tagList, String head, String body) {
		final BlockTag tag = tagConstructor.construct(head, body, tagPriority, tagFeatureNode);
		if (tag != null) {
			tagList.add(tag);
		}
	}

	public final List<BlockTag> getGeneralTags() {
		return generalTags;
	}

	public final List<BlockTag> getFeatureTags() {
		return featureTags;
	}

	public boolean addExtraFilters() {
		return false;
	}

}
