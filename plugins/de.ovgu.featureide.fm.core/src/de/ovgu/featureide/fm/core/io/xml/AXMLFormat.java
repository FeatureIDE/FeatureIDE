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

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;
import org.xml.sax.SAXParseException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Prints a feature model in XML format.
 *
 * @author Sebastian Krieter
 */
public abstract class AXMLFormat<T> extends APersistentFormat<T> implements IPersistentFormat<T>, XMLFeatureModelTags {

	private static final String SUFFIX = "xml";

	protected T object;

	/**
	 * @param nodeList
	 * @return The child nodes from type Element of the given NodeList.
	 */
	protected static final List<Element> getElements(NodeList nodeList) {
		final ArrayList<Element> elements = new ArrayList<>(nodeList.getLength());
		for (int temp = 0; temp < nodeList.getLength(); temp++) {
			final org.w3c.dom.Node nNode = nodeList.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				final Element eElement = (Element) nNode;
				elements.add(eElement);
			}
		}
		return elements;
	}

	@Override
	public String getSuffix() {
		return SUFFIX;
	}

	@Override
	public ProblemList read(T object, CharSequence source) {
		this.object = object;

		final ProblemList lastWarnings = new ProblemList();
		try {
			final Document doc = DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument();
			SAXParserFactory.newInstance().newSAXParser().parse(new InputSource(new StringReader(source.toString())), new PositionalXMLHandler(doc));
			doc.getDocumentElement().normalize();
			readDocument(doc, lastWarnings);
		} catch (final SAXParseException e) {
			lastWarnings.add(new Problem(e, e.getLineNumber()));
		} catch (final UnsupportedModelException e) {
			lastWarnings.add(new Problem(e, e.lineNumber));
		} catch (final Exception e) {
			lastWarnings.add(new Problem(e));
		}

		return lastWarnings;
	}

	@Override
	public String write(T object) {
		this.object = object;

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
			return "";
		}
		final Document doc = db.newDocument();
		// Create the XML Representation
		writeDocument(doc);

		try (StringWriter stringWriter = new StringWriter()) {
			final StreamResult streamResult = new StreamResult(stringWriter);
			final TransformerFactory factory = TransformerFactory.newInstance();
			factory.setAttribute("indent-number", new Integer(4));
			final Transformer transformer = factory.newTransformer();
			transformer.setOutputProperty(OutputKeys.METHOD, SUFFIX);
			transformer.setOutputProperty(OutputKeys.INDENT, YES);
			transformer.transform(new DOMSource(doc), streamResult);
			return streamResult.getWriter().toString();
		} catch (final IOException | TransformerException e) {
			Logger.logError(e);
			return "";
		}
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	protected final boolean supportsContent(LazyReader reader, Pattern pattern) {
		if (supportsRead()) {
			final Matcher matcher = pattern.matcher("");
			do {
				matcher.reset(reader);
				if (matcher.find()) {
					return true;
				}
			} while (matcher.hitEnd() && reader.expand());
		}
		return false;
	}

	/**
	 * Reads an XML-Document.
	 *
	 * @param doc document to read
	 * @param warnings list of warnings / errors that occur during read
	 */
	protected abstract void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException;

	/**
	 * Writes an XML-Document.
	 *
	 * @param doc document to write
	 */
	protected abstract void writeDocument(Document doc);

}
