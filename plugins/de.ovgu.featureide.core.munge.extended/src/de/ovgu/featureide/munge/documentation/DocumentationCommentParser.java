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
package de.ovgu.featureide.munge.documentation;

import org.prop4j.NodeReader;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	private final NodeReader nodeReader = new NodeReader();

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];

		boolean featureHead = false;
		// Type
		if (typeString.equals("general")) {
			tagFeatureNode = null;
		} else if (typeString.equals("feature")) {
			featureHead = true;
		} else {
			// warning?
			tagFeatureNode = null;
			tagPriority = 0;
		}

		// Priority
		if (parts.length > 1) {
			try {
				tagPriority = Integer.parseInt(parts[parts.length - 1]);
				if (featureHead) {
					if (parts.length > 2) {
						final StringBuilder sb = new StringBuilder();
						for (int i = 1; i < (parts.length - 1); i++) {
							sb.append(parts[i]);
							sb.append(' ');
						}
						tagFeatureNode = nodeReader.stringToNode(sb.toString());
					} else {
						// warning?
						tagFeatureNode = null;
					}
				}
			} catch (final NumberFormatException e) {
				tagPriority = 0;

				if (featureHead) {
					final StringBuilder sb = new StringBuilder();
					for (int i = 1; i < parts.length; i++) {
						sb.append(parts[i]);
						sb.append(' ');
					}
					tagFeatureNode = nodeReader.stringToNode(sb.toString());
				}
			}
		} else {
			tagPriority = 0;
		}
	}

	@Override
	public boolean addExtraFilters() {
		return true;
	}

}
