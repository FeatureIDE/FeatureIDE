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

import static de.ovgu.featureide.fm.core.localization.StringTable.YES;

import java.io.BufferedReader;
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
import de.ovgu.featureide.fm.core.io.Problem.Severity;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Prints a feature model in XML format.
 *
 * @author Sebastian Krieter
 */
public abstract class AXMLFormat<T> extends APersistentFormat<T> implements IPersistentFormat<T>, XMLFeatureModelTags {

	public static final String FILE_EXTENSION = "xml";

	private static final Pattern completeTagPattern = Pattern.compile("<(\\w+)[^\\/]*>.*<\\/\\1.*>");
	private static final Pattern incompleteTagPattern = Pattern.compile("(<\\w+[^\\/>]*>)|(<\\/\\w+[^>]*>)");

	protected T object;

	/**
	 * Returns a list of elements within the given node list.
	 *
	 * @param nodeList the node list.
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

	protected String prettyPrint(String text) {
		final StringBuilder result = new StringBuilder();
		int indentLevel = 0;
		try (final BufferedReader reader = new BufferedReader(new StringReader(text))) {
			for (String line = reader.readLine(); line != null; line = reader.readLine()) {
				final String trimmedLine = line.trim();
				if (!trimmedLine.isEmpty()) {
					if (completeTagPattern.matcher(trimmedLine).matches()) {
						appendLine(result, indentLevel, trimmedLine);
					} else {
						final Matcher matcher = incompleteTagPattern.matcher(trimmedLine);
						int start = 0;
						while (matcher.find()) {
							appendLine(result, indentLevel, trimmedLine.substring(start, matcher.start()));
							final String openTag = matcher.group(1);
							final String closeTag = matcher.group(2);
							if (openTag != null) {
								appendLine(result, indentLevel, openTag);
								indentLevel++;
							} else if (closeTag != null) {
								indentLevel--;
								appendLine(result, indentLevel, closeTag);
							}
							start = matcher.end();
						}
						appendLine(result, indentLevel, trimmedLine.substring(start, trimmedLine.length()));
					}
				}
			}
		} catch (final IOException e) {
			Logger.logError(e);
		}
		return result.toString();
	}

	private void appendLine(final StringBuilder result, int indentLevel, String line) {
		final String trimmedLine = line.trim();
		if (!trimmedLine.isEmpty()) {
			for (int i = 0; i < indentLevel; i++) {
				result.append("\t");
			}
			result.append(trimmedLine);
			result.append("\n");
		}
	}

	protected List<Element> getElement(final Element element, final String nodeName, boolean allowEmpty) throws UnsupportedModelException {
		final List<Element> elements = getElements(element.getElementsByTagName(nodeName));
		if (elements.size() != 1) {
			if (elements.size() > 1) {
				throwWarning("Multiple nodes of " + nodeName + " defined.", element);
			} else if (!allowEmpty) {
				throwError("Node " + nodeName + " not defined!", element);
			}
		}
		return elements;
	}

	protected List<Element> getElement(final Document document, final String nodeName, boolean allowEmpty) throws UnsupportedModelException {
		final List<Element> elements = getElements(document.getElementsByTagName(nodeName));
		if (elements.size() != 1) {
			if (elements.size() > 1) {
				addProblem(new Problem("Multiple nodes of " + nodeName + " defined.", 0, Severity.WARNING));
			} else if (!allowEmpty) {
				throwError("Node " + nodeName + " not defined!", document);
			}
		}
		return elements;
	}

	/**
	 * Throws an error that will be used for error markers
	 *
	 * @param message The error message
	 * @param node The node that causes the error. this node is used for positioning.
	 */
	protected static void throwError(String message, org.w3c.dom.Node node) throws UnsupportedModelException {
		final Object userData = node.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME);
		throw new UnsupportedModelException(message, userData == null ? 0 : Integer.parseInt(userData.toString()));
	}

	protected void addToProblemsList(String message, org.w3c.dom.Node node) {
		addProblem(new Problem(message, Integer.parseInt(node.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME).toString()),
				de.ovgu.featureide.fm.core.io.Problem.Severity.ERROR));
	}

	protected void throwWarning(String message, org.w3c.dom.Node node) {
		addProblem(new Problem(message, Integer.parseInt(node.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME).toString()), Severity.WARNING));
	}

	/**
	 * Can be overwritten be implementing classes to control how to handle problems. Does nothing on default.
	 *
	 * @param problem a problem.
	 */
	protected void addProblem(final Problem problem) {}

	@Override
	public String getSuffix() {
		return FILE_EXTENSION;
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
			factory.setAttribute("indent-number", Integer.valueOf(4));
			final Transformer transformer = factory.newTransformer();
			transformer.setOutputProperty(OutputKeys.METHOD, FILE_EXTENSION);
			transformer.setOutputProperty(OutputKeys.INDENT, YES);
			transformer.transform(new DOMSource(doc), streamResult);
			return prettyPrint(streamResult.getWriter().toString());
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

	protected final boolean supportsContent(CharSequence content, Pattern pattern) {
		return supportsRead() && pattern.matcher(content).find();
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
