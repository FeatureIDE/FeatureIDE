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
package de.ovgu.featureide.fm.core.io.xml;

import static de.ovgu.featureide.fm.core.localization.StringTable.YES;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.io.AbstractObjectWriter;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Prints a feature model in XML format.
 *
 * @deprecated Use {@link AXMLFormat} and {@link FileHandler} instead.
 *
 * @author Fabian Wielgorz
 * @author Dariusz Krolikowski
 * @author Maik Lampe
 * @author Jens Meinicke
 */
@Deprecated
public abstract class AbstractXMLFeatureModelWriter<T> extends AbstractObjectWriter<T> implements XMLFeatureModelTags {

	/**
	 * Creates a new writer and sets the feature model to write out.
	 *
	 * @param object the structure to write
	 */
	public AbstractXMLFeatureModelWriter(T object) {
		setObject(object);
	}

	/**
	 * Creates XML-Document
	 *
	 * @param doc document to write
	 */
	protected abstract void createXmlDoc(Document doc);

	/**
	 * Inserts indentations into the text
	 *
	 * @param text
	 * @return
	 */
	private static String prettyPrint(String text) {
		final StringBuilder result = new StringBuilder();
		String line;
		int indentLevel = 0;
		final BufferedReader reader = new BufferedReader(new StringReader(text));
		try {
			line = reader.readLine();
			while (line != null) {
				if (line.startsWith("</")) {
					indentLevel--;
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
				}

				else if (line.startsWith("<")) {
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
					if (!line.contains("</")) {
						indentLevel++;
					}
				} else {
					for (int i = 0; i < indentLevel; i++) {
						result.append("\t");
					}
				}
				result.append(line + "\n");
				if (line.contains("/>")) {
					indentLevel--;
				}
				line = reader.readLine();
			}
		} catch (final IOException e) {
			Logger.logError(e);
		}
		return result.toString();
	}

	@Override
	public String writeToString() {
		// Create Empty DOM Document
		final DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		dbf.setNamespaceAware(true);
		dbf.setIgnoringComments(true);
		dbf.setIgnoringElementContentWhitespace(false);
		dbf.setCoalescing(true);
		dbf.setExpandEntityReferences(true);
		DocumentBuilder db = null;
		try {
			db = dbf.newDocumentBuilder();
		} catch (final ParserConfigurationException pce) {
			Logger.logError(pce);
		}
		final Document doc = db.newDocument();
		// Create the Xml Representation
		createXmlDoc(doc);

		// Transform the Xml Representation into a String
		Transformer transfo = null;
		try {
			transfo = TransformerFactory.newInstance().newTransformer();
		} catch (final TransformerConfigurationException e) {
			Logger.logError(e);
		} catch (final TransformerFactoryConfigurationError e) {
			Logger.logError(e);
		}

		transfo.setOutputProperty(OutputKeys.METHOD, "xml");
		transfo.setOutputProperty(OutputKeys.INDENT, YES);
		final StreamResult result = new StreamResult(new StringWriter());
		final DOMSource source = new DOMSource(doc);
		try {
			transfo.transform(source, result);
		} catch (final TransformerException e) {
			Logger.logError(e);
		}

		return prettyPrint(result.getWriter().toString());
	}
}
