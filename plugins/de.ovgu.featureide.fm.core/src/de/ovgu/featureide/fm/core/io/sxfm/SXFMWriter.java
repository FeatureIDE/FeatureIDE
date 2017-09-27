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
package de.ovgu.featureide.fm.core.io.sxfm;

import static de.ovgu.featureide.fm.core.localization.StringTable.CANT_DETERMINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONNECTIONTYPE_OF_ROOTFEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.YES;

import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

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
import org.prop4j.NodeWriter;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.FeatureUtilsLegacy;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.AbstractObjectWriter;

/**
 * Prints feature models in the SXFM format.
 *
 * @author Fabian Wielgorz
 */
@Deprecated
public class SXFMWriter extends AbstractObjectWriter<FeatureModel> {

	private final static String[] symbols = new String[] { "~", " and ", " or ", "", "", ", ", "", "", "" };

	private final IFeatureModel featureModel;

	/**
	 * Creates a new writer and sets the feature model to write out.
	 *
	 * @param featureModel the structure to write
	 */
	public SXFMWriter(de.ovgu.featureide.fm.core.FeatureModel featureModel) {
		this.featureModel = FeatureUtilsLegacy.convert(featureModel);
		setObject(featureModel);
	}

	@Override
	public String writeToString() {
		// Create Empty DOM Document
		final DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		dbf.setNamespaceAware(true);
		dbf.setIgnoringComments(true);
		dbf.setIgnoringElementContentWhitespace(false);
		dbf.setCoalescing(false);
		dbf.setExpandEntityReferences(false);
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
		transfo.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, YES);
		final StreamResult result = new StreamResult(new StringWriter());
		final DOMSource source = new DOMSource(doc);
		try {
			transfo.transform(source, result);
		} catch (final TransformerException e) {
			Logger.logError(e);
		}
		return result.getWriter().toString();
	}

	/**
	 * Creates the DOM Document Representation from the feature model fmodel by using createXmlDocRec
	 *
	 * @param doc Document where the feature model is put
	 */
	private void createXmlDoc(Document doc) {
		final Element elem = doc.createElement("feature_model");
		elem.setAttribute("name", "FeatureIDE model");
		doc.appendChild(elem);
		final Node featTree = doc.createElement("feature_tree");
		elem.appendChild(featTree);
		featTree.appendChild(doc.createTextNode("\n"));
		createXmlDocRec(doc, featTree, featureModel.getStructure().getRoot().getFeature(), false, "");
		createPropositionalConstraints(doc, elem);
	}

	/**
	 * Creates the DOM Document Representation from the feature model fmodel by recursively building the Nodes
	 *
	 * @param doc Document where the feature model is put
	 * @param nod Current Node in the Document Tree
	 * @param feat Current Feature in the feature model Tree
	 * @param andMode true if the connection between the current feature and its parent is of the type "and", false otherwise
	 * @param indent indentation of the parent feature
	 */
	private void createXmlDocRec(Document doc, Node nod, IFeature feat, boolean andMode, String indent) {
		String newIndent;
		Node textNode;
		LinkedList<IFeature> children;
		boolean nextAndMode = false;
		if (feat == null) {
			return;
		}
		final String fName = feat.getName();
		if (feat.getStructure().isRoot()) {
			textNode = doc.createTextNode(":r " + fName + "(" + fName + ")\n");
			newIndent = "\t";
		} else if (andMode) {
			if (feat.getStructure().isMandatory()) {
				textNode = doc.createTextNode(indent + ":m " + fName + "(" + fName + ")\n");
			} else {
				textNode = doc.createTextNode(indent + ":o " + fName + "(" + fName + ")\n");
			}
		} else {
			textNode = doc.createTextNode(indent + ": " + fName + "(" + fName + ")\n");
		}
		nod.appendChild(textNode);
		children = new LinkedList<>(Functional.toList(FeatureUtils.convertToFeatureList(feat.getStructure().getChildren())));
		if (children.isEmpty()) {
			return;
		}
		if (feat.getStructure().isAnd()) {
			nextAndMode = true;
			newIndent = indent + "\t";
		} else if (feat.getStructure().isOr()) {
			textNode = doc.createTextNode(indent + "\t:g [1,*]\n");
			nod.appendChild(textNode);
			newIndent = indent + "\t\t";
			nextAndMode = false;
		} else if (feat.getStructure().isAlternative()) {
			textNode = doc.createTextNode(indent + "\t:g [1,1]\n");
			nod.appendChild(textNode);
			newIndent = indent + "\t\t";
			nextAndMode = false;
		} else {
			throw new IllegalStateException(CANT_DETERMINE + CONNECTIONTYPE_OF_ROOTFEATURE);
		}

		final Iterator<IFeature> i = children.iterator();
		while (i.hasNext()) {
			createXmlDocRec(doc, nod, i.next(), nextAndMode, newIndent);
		}
	}

	/**
	 * Inserts the tags concerning propositional constraints into the DOM document representation
	 *
	 * @param doc
	 * @param FeatMod Parent node for the propositional nodes
	 */
	private void createPropositionalConstraints(Document doc, Node FeatMod) {
		// add a node for constraints in any case
		final Node propConstr = doc.createElement("constraints");
		FeatMod.appendChild(propConstr);
		final Node newNode = doc.createTextNode("\n");
		propConstr.appendChild(newNode);
		if (featureModel.getConstraints().isEmpty()) {
			return;
		}
		// as before
		int i = 1;
		for (final org.prop4j.Node node : FeatureUtils.getPropositionalNodes(featureModel.getConstraints())) {
			// avoid use of parenthesis from the beginning
			// org.prop4j.Node cnf = node.clone().toCNF();

			final org.prop4j.Node cnf = node.toCNF();

			final ArrayList<org.prop4j.Node> literalList = new ArrayList<>();
			if (cnf instanceof And) {
				for (final org.prop4j.Node child : cnf.getChildren()) {
					if (child instanceof Or) {
						literalList.addAll(Arrays.asList(child.getChildren()));
					} else {
						literalList.add(child);
					}
				}
			} else if (cnf instanceof Or) {
				literalList.addAll(Arrays.asList(cnf.getChildren()));
			} else {
				literalList.add(cnf);
			}

			final HashSet<org.prop4j.Node> literalSet = new HashSet<>(literalList.size());
			boolean invalid = false;
			for (final org.prop4j.Node literal : literalList) {
				final Literal negativeliteral = ((Literal) literal).clone();
				negativeliteral.flip();

				if (literalSet.contains(negativeliteral)) {
					invalid = true;
				} else {
					literalSet.add(literal);
				}
			}

			if (!invalid) {
				if (cnf instanceof And) {
					for (final org.prop4j.Node child : cnf.getChildren()) {
						i = createConstraint(doc, propConstr, i, child);
					}
				} else {
					i = createConstraint(doc, propConstr, i, cnf);
				}
			}
		}
	}

	private int createConstraint(Document doc, Node propConstr, int i, org.prop4j.Node node) {
		Node newNode;
		final NodeWriter nw = new NodeWriter(node);
		nw.setSymbols(symbols);
		nw.setEnforceBrackets(true);
		String nodeString = nw.nodeToString();
		// remove the external parenthesis
		if ((nodeString.startsWith("(")) && (nodeString.endsWith(")"))) {
			nodeString = nodeString.substring(1, nodeString.length() - 1);
		}
		// replace the space before a variable
		nodeString = nodeString.replace("~ ", "~");
		newNode = doc.createTextNode("C" + i + ":" + nodeString + "\n");
		propConstr.appendChild(newNode);
		return ++i;
	}

	public FeatureModel getFeatureModel() {
		return object;
	}

	public void setFeatureModel(FeatureModel featureModel) {
		object = featureModel;
	}

}
