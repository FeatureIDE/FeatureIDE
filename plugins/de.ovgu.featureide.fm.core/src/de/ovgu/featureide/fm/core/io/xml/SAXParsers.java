/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.xml;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.xml.sax.SAXException;
import org.xml.sax.SAXNotRecognizedException;
import org.xml.sax.SAXNotSupportedException;

/**
 * Creates the SAX parsers used to read FeatureIDE's XML files.
 *
 * @author Philipp Hehnle
 */
public final class SAXParsers {

	/**
	 * JDK property that limits how deeply XML elements may be nested. Since JDK 24 the default limit is 100, which large feature models exceed, because every
	 * operator of a constraint (e.g. &lt;conj&gt;) is one nesting level.
	 */
	private static final String MAX_ELEMENT_DEPTH = "jdk.xml.maxElementDepth";

	private SAXParsers() {}

	/**
	 * @return a new SAX parser without a limit on the nesting depth of elements (0 means no limit), as with JDK versions before 24.
	 */
	public static SAXParser newSAXParser() throws ParserConfigurationException, SAXException {
		final SAXParser parser = SAXParserFactory.newInstance().newSAXParser();
		try {
			parser.setProperty(MAX_ELEMENT_DEPTH, "0");
		} catch (SAXNotRecognizedException | SAXNotSupportedException e) {
			// not the JDK's parser, which has no such limit
		}
		return parser;
	}
}
