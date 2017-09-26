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
package de.ovgu.featureide.antenna.documentation;

import org.prop4j.NodeReader;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	private final NodeReader nodeReader = new NodeReader();

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];
		int prioIndex = 1;

		// Type
		if (typeString.equals("general")) {
			tagFeatureNode = null;
		} else if (typeString.equals("feature")) {
			if (parts.length > prioIndex) {
				tagFeatureNode = nodeReader.stringToNode(parts[prioIndex++]);
			} else {
				// warning?
				tagFeatureNode = null;
			}
		} else {
			// warning?
			tagFeatureNode = null;
			tagPriority = 0;
		}

		// Priority
		if (parts.length > prioIndex) {
			try {
				tagPriority = Integer.parseInt(parts[prioIndex]);
			} catch (final NumberFormatException e) {
				// warning?
				tagPriority = 0;
			}
		} else {
			tagPriority = 0;
		}
	}

}
