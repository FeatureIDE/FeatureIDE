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

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.core.signature.ProjectSignatures;

/**
 * Creates a {@link BlockTag} from a given line in a Javadoc comment.</br> Is used by {@link ADocumentationCommentParser}.
 *
 * @author Sebastian Krieter
 */
class BlockTagConstructor {

	private final ProjectSignatures projectSignatures;

	private String head, body;
	private Node featureNode;
	private int priority;

	public BlockTagConstructor(ProjectSignatures projectSignatures) {
		this.projectSignatures = projectSignatures;
	}

	public BlockTag construct(String head, String body, int priority, Node featureNode) {
		this.head = head;
		this.body = body;
		this.featureNode = featureNode;
		this.priority = priority;

		switch (head) {
		case "":
			if (body.isEmpty()) {
				return null;
			}
			return construct(0, BlockTag.TAG_DESCRIPTION);
		case "@author":
			return construct(Integer.MAX_VALUE, BlockTag.TAG_AUTHOR);
		case "@version":
			return construct(0, BlockTag.TAG_VERSION);
		case "@param":
			construct(1, BlockTag.TAG_PARAM);
		case "@return":
			return construct(0, BlockTag.TAG_RETURN);
		case "@throws":
		case "@exception":
			construct(1, BlockTag.TAG_THROWS);
		case "@see":
			return construct(Integer.MAX_VALUE, BlockTag.TAG_SEE);
		case "@since":
			return construct(0, BlockTag.TAG_SINCE);
		case "@deprecated":
			return construct(0, BlockTag.TAG_DEPRECATED);
		case "@serial":
		case "@serialData":
			return construct(0, BlockTag.TAG_SERIAL);
		case "@serialField":
			return construct(2, BlockTag.TAG_SERIALFIELD);
		default:
			return construct(0, BlockTag.TAG_UNKNOWN);
		}
	}

	private BlockTag construct(int keyParts, int type) {
		final int featureID = (featureNode instanceof Literal) ? projectSignatures.getFeatureID((String) ((Literal) featureNode).var) : -1;

		switch (keyParts) {
		case 0:
			return new BlockTag(head, body, type, priority, featureID, featureNode);
		case Integer.MAX_VALUE:
			return new BlockTag(head + " " + body, "", type, priority, featureID, featureNode);
		default:
			final Pattern whiteSpace = Pattern.compile("\\s+");
			final Matcher m = whiteSpace.matcher(body);

			int countParts = 0, startIndex = -1, endIndex = 0;
			while (m.find() && (countParts++ < keyParts)) {
				startIndex = m.start();
				endIndex = m.end();
			}
			return (startIndex > -1)
				? new BlockTag(head + " " + body.substring(0, startIndex), body.substring(endIndex), type, priority, featureID, featureNode)
				: new BlockTag(head + " " + body, "", type, priority, featureID, featureNode);
		}
	}

	public ProjectSignatures getProjectSignatures() {
		return projectSignatures;
	}

}
