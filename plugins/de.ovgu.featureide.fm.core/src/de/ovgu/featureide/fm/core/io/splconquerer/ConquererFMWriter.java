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
package de.ovgu.featureide.fm.core.io.splconquerer;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHILD;
import static de.ovgu.featureide.fm.core.localization.StringTable.CLASSES;
import static de.ovgu.featureide.fm.core.localization.StringTable.CLAUSE;
import static de.ovgu.featureide.fm.core.localization.StringTable.COMMULATIVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.DYNAMIC;
import static de.ovgu.featureide.fm.core.localization.StringTable.ELEMENT;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXCLUDES;
import static de.ovgu.featureide.fm.core.localization.StringTable.OPTIONAL;
import static de.ovgu.featureide.fm.core.localization.StringTable.ORDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.REQUIRES;
import static de.ovgu.featureide.fm.core.localization.StringTable.TYPE;
import static de.ovgu.featureide.fm.core.localization.StringTable.YES;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;

/**
 * Prints a feature model in SPLConqueror format.
 *
 * @author Dariusz Krolikowski
 * @author Maik Lampe
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class ConquererFMWriter extends APersistentFormat<IFeatureModel> implements IFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + ConquererFMWriter.class.getSimpleName();

	private IFeatureModel featureModel;

	private Map<String, Set<String>> require, exclude;

	/**
	 * Creates XML-Document
	 *
	 * @param doc document to write
	 */
	private void createXmlDoc(Document doc) {
		final Element plm = doc.createElement("plm");
		doc.appendChild(plm);
		plm.setAttribute("name", featureModel.getStructure().getRoot().getFeature().getName());
		plm.setAttribute("canReuseInstance", "true");

		require = new HashMap<String, Set<String>>();
		exclude = new HashMap<String, Set<String>>();
		final List<Node> furtherNodes = new LinkedList<Node>();
		final List<Node> nodes = Functional.toList(FeatureUtils.getPropositionalNodes(featureModel.getConstraints()));
		final Node[] nodeArray = nodes.toArray(new Node[nodes.size()]);
		Node node = new And(nodeArray);
		if (node.getChildren().length > 0) {
			node = node.toCNF();
			if (!(node instanceof And)) {
				node = new And(node);
			}
			for (final Node child : node.getChildren()) {
				if ((child instanceof Or) && (child.getChildren().length == 2)) {
					Literal literalA = (Literal) child.getChildren()[0];
					Literal literalB = (Literal) child.getChildren()[1];
					if (!literalA.positive || !literalB.positive) {
						if (literalA.positive) {
							final Literal temp = literalA;
							literalA = literalB;
							literalB = temp;
						}
						if (literalB.positive) {
							Set<String> set = require.get(literalA.var);
							if (set == null) {
								set = new HashSet<String>();
								require.put(literalA.var.toString(), set);
							}
							set.add(literalB.var.toString());
						} else {
							Set<String> set = exclude.get(literalA.var);
							if (set == null) {
								set = new HashSet<String>();
								exclude.put(literalA.var.toString(), set);
							}
							set.add(literalB.var.toString());
						}
					} else {
						furtherNodes.add(child);
					}
				} else {
					furtherNodes.add(child);
				}
			}
		}

		initializeIDs();
		generateSubtree(doc, plm, featureModel.getStructure().getRoot().getFeature());

		plm.appendChild(doc.createElement("properties"));

		final Element furtherConstraints = doc.createElement("furtherConstraints");
		plm.appendChild(furtherConstraints);
		for (final Node child : furtherNodes) {
			final Element clause = doc.createElement(CLAUSE);
			furtherConstraints.appendChild(clause);
			clause.appendChild(doc.createTextNode(child.toString()));
		}
	}

	private void generateSubtree(Document doc, Element node, IFeature feature) {
		if (!feature.getStructure().isRoot()) {
			generateElement(doc, node, feature);
		}

		for (final IFeature child : FeatureUtils.convertToFeatureList(feature.getStructure().getChildren())) {
			generateSubtree(doc, node, child);
		}
	}

	private void generateElement(Document doc, Element node, IFeature feature) {
		final Element element = doc.createElement(ELEMENT);
		node.appendChild(element);
		element.setAttribute("id", getID(feature.getName()));
		element.setAttribute("name", feature.getName());
		element.setAttribute(TYPE, "feature");
		element.setAttribute(OPTIONAL, feature.getStructure().isMandatory() ? "false" : "true");
		element.setAttribute(DYNAMIC, "false");

		element.appendChild(doc.createElement("path_absolut"));
		element.appendChild(doc.createElement("path_relativ"));

		if (!feature.getStructure().getParent().isRoot()) {
			final Element parentElement = doc.createElement("parentElement");
			element.appendChild(parentElement);
			final Element id = doc.createElement("id");
			parentElement.appendChild(id);
			id.appendChild(doc.createTextNode(getID(FeatureUtils.getParent(feature).getName())));
		}

		final Element constraints = doc.createElement("constraints");
		element.appendChild(constraints);

		final Element alternative = doc.createElement("constraint");
		constraints.appendChild(alternative);
		alternative.setAttribute(TYPE, "alternative");
		if (!feature.getStructure().isRoot() && feature.getStructure().getParent().isAlternative()) {
			for (final IFeature childFeature : FeatureUtils.convertToFeatureList(feature.getStructure().getParent().getChildren())) {
				if (childFeature != feature) {
					final Element constraint_element = doc.createElement("constraint_element");
					alternative.appendChild(constraint_element);
					final Element id = doc.createElement("id");
					constraint_element.appendChild(id);
					id.appendChild(doc.createTextNode(getID(childFeature.getName())));
					final Element name = doc.createElement("name");
					constraint_element.appendChild(name);
					name.appendChild(doc.createTextNode(childFeature.getName()));
				}
			}
		}

		final Element commulative = doc.createElement("constraint");
		constraints.appendChild(commulative);
		commulative.setAttribute(TYPE, COMMULATIVE);
		if (!feature.getStructure().isRoot() && feature.getStructure().getParent().isOr()) {
			for (final IFeature childFeature : FeatureUtils.convertToFeatureList(feature.getStructure().getParent().getChildren())) {
				if (childFeature != feature) {
					final Element constraint_element = doc.createElement("constraint_element");
					commulative.appendChild(constraint_element);
					final Element id = doc.createElement("id");
					constraint_element.appendChild(id);
					id.appendChild(doc.createTextNode(getID(childFeature.getName())));
					final Element name = doc.createElement("name");
					constraint_element.appendChild(name);
					name.appendChild(doc.createTextNode(childFeature.getName()));
				}
			}
		}

		final Element requires = doc.createElement("constraint");
		constraints.appendChild(requires);
		requires.setAttribute(TYPE, REQUIRES);
		final Set<String> requireFeature = require.get(feature.getName());
		if (requireFeature != null) {
			for (final String childFeature : requireFeature) {
				final Element constraint_element = doc.createElement("constraint_element");
				requires.appendChild(constraint_element);
				final Element id = doc.createElement("id");
				constraint_element.appendChild(id);
				id.appendChild(doc.createTextNode(getID(childFeature)));
				final Element name = doc.createElement("name");
				constraint_element.appendChild(name);
				name.appendChild(doc.createTextNode(childFeature));
			}
		}

		final Element excludes = doc.createElement("constraint");
		constraints.appendChild(excludes);
		excludes.setAttribute(TYPE, EXCLUDES);
		final Set<String> excludeFeature = exclude.get(feature.getName());
		if (excludeFeature != null) {
			for (final String childFeature : excludeFeature) {
				final Element constraint_element = doc.createElement("constraint_element");
				excludes.appendChild(constraint_element);
				final Element id = doc.createElement("id");
				constraint_element.appendChild(id);
				id.appendChild(doc.createTextNode(getID(childFeature)));
				final Element name = doc.createElement("name");
				constraint_element.appendChild(name);
				name.appendChild(doc.createTextNode(childFeature));
			}
		}

		final Element childElements = doc.createElement("childElements");
		element.appendChild(childElements);
		for (final IFeature childFeature : FeatureUtils.convertToFeatureList(feature.getStructure().getChildren())) {
			final Element child = doc.createElement(CHILD);
			childElements.appendChild(child);
			child.setAttribute(OPTIONAL, childFeature.getStructure().isMandatory() ? "false" : "true");
			final Element id = doc.createElement("id");
			child.appendChild(id);
			id.appendChild(doc.createTextNode(getID(childFeature.getName())));
		}

		element.appendChild(doc.createElement(ORDER));
		element.appendChild(doc.createElement(CLASSES));
	}

	/**
	 * Inserts indentations into the text
	 *
	 * @param text
	 * @return
	 */
	private String prettyPrint(String text) {
		final StringBuilder result = new StringBuilder();
		String line;
		int indentLevel = 0;
		final BufferedReader reader = new BufferedReader(new StringReader(text));
		try {
			reader.readLine(); // hack to remove first line
			line = reader.readLine();
			while (line != null) {
				if (line.startsWith("</")) {
					indentLevel--;
					for (int i = 0; i < indentLevel; i++) {
						result.append('\t');
					}
				}

				else if (line.startsWith("<")) {
					for (int i = 0; i < indentLevel; i++) {
						result.append('\t');
					}
					if (!line.contains("</")) {
						indentLevel++;
					}
				} else {
					for (int i = 0; i < indentLevel; i++) {
						result.append('\t');
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

	public String writeToString(IFeatureModel featureModel) {
		this.featureModel = featureModel;
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

	private HashMap<String, Integer> ids;

	private void initializeIDs() {
		ids = new HashMap<String, Integer>();
		initializeIDs(featureModel.getStructure().getRoot().getFeature());
	}

	private void initializeIDs(IFeature feature) {
		getID(feature.getName());
		for (final IFeature child : FeatureUtils.convertToFeatureList(feature.getStructure().getChildren())) {
			initializeIDs(child);
		}
	}

	private String getID(String feature) {
		Integer id = ids.get(feature);
		if (id != null) {
			return id.toString();
		}
		id = ids.size() + 1;
		ids.put(feature, id);
		return id.toString();
	}

	@Override
	public String write(IFeatureModel object) {
		return writeToString(object);
	}

	@Override
	public String getSuffix() {
		return "xml";
	}

	@Override
	public ConquererFMWriter getInstance() {
		return new ConquererFMWriter();
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "SPL Conquerer";
	}

}
