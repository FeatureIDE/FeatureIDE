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

import static de.ovgu.featureide.fm.core.localization.StringTable.ABSTRACT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.COMMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDDEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.MANDATORY;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOT;
import static de.ovgu.featureide.fm.core.localization.StringTable.WRONG_SYNTAX;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;

import javax.xml.parsers.ParserConfigurationException;

import org.prop4j.And;
import org.prop4j.AtMost;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlPropertyLoader.PropertiesParser;

/**
 * Parses a FeatureModel from XML
 *
 * @deprecated Use {@link XmlFeatureModelFormat} and {@link FileHandler} instead.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
@Deprecated
public class XmlFeatureModelReader extends AbstractFeatureModelReader implements XMLFeatureModelTags {

	public XmlFeatureModelReader(IFeatureModel featureModel) {
		setFeatureModel(featureModel);
	}

	@Override
	protected synchronized void parseInputStream(final InputStream inputStream) throws UnsupportedModelException {
		featureModel.reset();
// TODO _interfaces Removed Code
//		featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures(true);
//		featureModel.getGraphicRepresenation().getLayout().verticalLayout(false);
		Document doc = null;
		try {
			doc = PositionalXMLReader.readXML(inputStream);
		} catch (final SAXParseException e) {
			throw new UnsupportedModelException(e.getMessage(), e.getLineNumber());
		} catch (final IOException e) {
			Logger.logError(e);
		} catch (final SAXException e) {
			Logger.logError(e);
		} catch (final ParserConfigurationException e) {
			Logger.logError(e);
		}
		doc.getDocumentElement().normalize();

		final Collection<PropertiesParser> customProperties = new ArrayList<>();

		for (final Element e : getElements(doc.getElementsByTagName(FEATURE_MODEL))) {
			setFeatureModelAttributes(e);
			parseStruct(e.getElementsByTagName(STRUCT));
			parseConstraints(e.getElementsByTagName(CONSTRAINTS));
			parseCalculations(e.getElementsByTagName(CALCULATIONS));
			parseComments(e.getElementsByTagName(COMMENTS));
			parseFeatureOrder(e.getElementsByTagName(FEATURE_ORDER));

			final XmlPropertyLoader propertyLoader = new XmlPropertyLoader(e.getElementsByTagName(PROPERTIES));
			customProperties.addAll(propertyLoader.parseProperties());
		}
		if (FeatureUtils.getRoot(featureModel) == null) {
			throw new UnsupportedModelException(WRONG_SYNTAX, 1);
		}

		importCustomProperties(customProperties, featureModel);

		// featureModel.handleModelDataLoaded();
	}

	private void importCustomProperties(Collection<PropertiesParser> customProperties, IFeatureModel featureModel) {
		for (final PropertiesParser parser : customProperties) {
			switch (parser.getType()) {
			case FEATURE_PROPERTIES_PARSER: {
				for (final String featureName : parser.getIdentifier()) {
					featureModel.getFeature(featureName).getCustomProperties().setEntrySet(parser.getPropertyEntries(featureName));
				}
			}
				break;
			default:
				throw new UnsupportedOperationException("Unkown property container parser type " + parser.getType());
			}
		}
	}

	/**
	 * @param nodeList
	 * @return The child nodes from type Element of the given NodeList.
	 */
	private ArrayList<Element> getElements(NodeList nodeList) {
		final ArrayList<Element> elements = new ArrayList<Element>(nodeList.getLength());
		for (int temp = 0; temp < nodeList.getLength(); temp++) {
			final org.w3c.dom.Node nNode = nodeList.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				final Element eElement = (Element) nNode;
				elements.add(eElement);
			}
		}
		return elements;
	}

	/**
	 * Adds attributes to the feature model
	 */
	private void setFeatureModelAttributes(Element eElement) {
		// TODO _interfaces Legacy Code
//		String algorithm = eElement.getAttribute(CHOSEN_LAYOUT_ALGORITHM);
//		if (!algorithm.equals("")) {
//			featureModel.getGraphicRepresenation().getLayout().setLayout(
//					Integer.parseInt(algorithm));
//		}
//		String layout = eElement.getAttribute(HORIZONTAL_LAYOUT);
//		if (layout.equals(TRUE)) {
//			featureModel.getGraphicRepresenation().getLayout().verticalLayout(false);
//		} else if (layout.equals(FALSE)) {
//			featureModel.getGraphicRepresenation().getLayout().verticalLayout(true);
//		}
//		String showHidden = eElement.getAttribute(SHOW_HIDDEN_FEATURES);
//		if (showHidden.equals(TRUE)) {
//			featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures(true);
//		} else if (showHidden.equals(FALSE)) {
//			featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures(false);
//		}
	}

	/**
	 * Parse the struct section to add features to the model.
	 */
	private void parseStruct(NodeList struct) throws UnsupportedModelException {
		for (final Element e : getElements(struct)) {
			parseFeatures(e.getChildNodes(), null);
		}
	}

	private void parseFeatures(NodeList nodeList, IFeature parent) throws UnsupportedModelException {
		for (final Element e : getElements(nodeList)) {
			final String nodeName = e.getNodeName();
			if (nodeName.equals(DESCRIPTION)) {
				/* case: description */
				String nodeValue = e.getFirstChild().getNodeValue();
				if (nodeValue != null) {
					nodeValue = nodeValue.replace("\t", "");
					nodeValue = nodeValue.substring(1, nodeValue.length() - 1);
					nodeValue = nodeValue.trim();
				}
				parent.getProperty().setDescription(nodeValue);
				continue;
			}
			boolean mandatory = false;
			boolean _abstract = false;
			boolean hidden = false;
			String name = "";
//			FMPoint featureLocation = null;
			if (e.hasAttributes()) {
				final NamedNodeMap nodeMap = e.getAttributes();
				for (int i = 0; i < nodeMap.getLength(); i++) {
					final org.w3c.dom.Node node = nodeMap.item(i);
					final String attributeName = node.getNodeName();
					final String attributeValue = node.getNodeValue();
					if (attributeName.equals(ABSTRACT)) {
						_abstract = attributeValue.equals(TRUE);
					} else if (attributeName.equals(MANDATORY)) {
						mandatory = attributeValue.equals(TRUE);
					} else if (attributeName.equals(NAME)) {
						name = attributeValue;
					} else if (attributeName.equals(HIDDEN)) {
						hidden = attributeValue.equals(TRUE);
					} else if (attributeName.equals(COORDINATES)) {
// TODO _interfaces Legacy Code
//						String subStringX = attributeValue.substring(0, attributeValue.indexOf(", "));
//						String subStringY = attributeValue.substring(attributeValue.indexOf(", ")+2);
//						try {
//							featureLocation = new FMPoint(Integer.parseInt (subStringX),
//										Integer.parseInt (subStringY));
//						} catch (NumberFormatException error) {
//							throwError(error.getMessage() + IS_NO_VALID_INTEGER_VALUE, e);
//						}
					} else {
						throwError("Unknown feature attribute: " + attributeName, e);
					}

				}
			}

			if (featureModel.getFeature(name) != null) {
				throwError("Duplicate entry for feature: " + name, e);
			}
			final IFeature f = FMFactoryManager.getFactory(featureModel).createFeature(featureModel, name);
			f.getStructure().setMandatory(true);
			if (nodeName.equals(AND)) {
				f.getStructure().setAnd();
			} else if (nodeName.equals(ALT)) {
				f.getStructure().setAlternative();
			} else if (nodeName.equals(OR)) {
				f.getStructure().setOr();
			} else if (nodeName.equals(FEATURE)) {

			} else {
				throwError("Unknown feature type: " + nodeName, e);
			}
			f.getStructure().setAbstract(_abstract);
			f.getStructure().setMandatory(mandatory);
			f.getStructure().setHidden(hidden);
			// TODO _interfaces Removed Code
//			if (featureLocation != null) {
//				f.getGraphicRepresenation().setLocation(featureLocation);
//			}
			featureModel.addFeature(f);
			if (parent == null) {
				featureModel.getStructure().setRoot(f.getStructure());
			} else {
				parent.getStructure().addChild(f.getStructure());
			}
			if (e.hasChildNodes()) {
				parseFeatures(e.getChildNodes(), f);
			}
		}
	}

	/**
	 * Parses the constraint section.
	 */
	private void parseConstraints(NodeList nodeList) throws UnsupportedModelException {
		for (final Element e : getElements(nodeList)) {
			for (final Element child : getElements(e.getChildNodes())) {
				final String nodeName = child.getNodeName();
				if (nodeName.equals(RULE)) {
					final IConstraint c =
						FMFactoryManager.getFactory(featureModel).createConstraint(featureModel, parseConstraints2(child.getChildNodes()).getFirst());
					if (child.hasAttributes()) {
						final NamedNodeMap nodeMap = child.getAttributes();
						for (int i = 0; i < nodeMap.getLength(); i++) {
							final org.w3c.dom.Node node = nodeMap.item(i);
							final String attributeName = node.getNodeName();
//							String attributeValue = node.getNodeValue();
							if (attributeName.equals(COORDINATES)) {
// TODO _interfaces Legacy Code
//								String subStringX = attributeValue.substring(0, attributeValue.indexOf(", "));
//								String subStringY = attributeValue.substring(attributeValue.indexOf(", ")+2);
//								try {
//									c.getGraphicRepresenation().setLocation(new FMPoint(Integer.parseInt (subStringX),
//												Integer.parseInt (subStringY)));
//								} catch (NumberFormatException error) {
//									throwError(error.getMessage() + IS_NO_VALID_INTEGER_VALUE, child);
//								}
							} else {
								throwError("Unknown constraint attribute: " + attributeName, node);
							}
						}
					}
					featureModel.addConstraint(c);
				} else {
					throwError("Unknown constraint node: " + nodeName, child);
				}
			}
		}
	}

	private LinkedList<Node> parseConstraints2(NodeList nodeList) throws UnsupportedModelException {
		final LinkedList<Node> nodes = new LinkedList<Node>();
		for (final Element e : getElements(nodeList)) {
			final String nodeName = e.getNodeName();
			if (nodeName.equals(DISJ)) {
				nodes.add(new Or(parseConstraints2(e.getChildNodes())));
			} else if (nodeName.equals(CONJ)) {
				nodes.add(new And(parseConstraints2(e.getChildNodes())));
			} else if (nodeName.equals(EQ)) {
				final LinkedList<Node> children = parseConstraints2(e.getChildNodes());
				nodes.add(new Equals(children.get(0), children.get(1)));
			} else if (nodeName.equals(IMP)) {
				final LinkedList<Node> children = parseConstraints2(e.getChildNodes());
				nodes.add(new Implies(children.get(0), children.get(1)));
			} else if (nodeName.equals(NOT)) {
				nodes.add(new Not((parseConstraints2(e.getChildNodes())).getFirst()));
			} else if (nodeName.equals(ATMOST1)) {
				nodes.add(new AtMost(1, parseConstraints2(e.getChildNodes())));
			} else if (nodeName.equals(VAR)) {
				final String featureName = e.getTextContent();
				if (featureModel.getFeature(featureName) != null) {
					nodes.add(new Literal(featureName));
				} else {
					throwError("Feature \"" + featureName + "\" does not exists", e);
				}
			} else {
				throwError("Unknown constraint type: " + nodeName, e);
			}
		}
		return nodes;
	}

	/**
	 * Parses the comment section.
	 */
	private void parseComments(NodeList nodeList) throws UnsupportedModelException {
		for (final Element e : getElements(nodeList)) {
			if (e.hasChildNodes()) {
				parseComments2(e.getChildNodes());
			}
		}
	}

	private void parseComments2(NodeList nodeList) throws UnsupportedModelException {
		for (final Element e : getElements(nodeList)) {
			if (e.getNodeName().equals(C)) {
				featureModel.getProperty().addComment(e.getTextContent());
			} else {
				throwError("Unknown comment attribute: " + e.getNodeName(), e);
			}
		}
	}

	/**
	 * Parses the feature order section.
	 */
	private void parseFeatureOrder(NodeList nodeList) throws UnsupportedModelException {
		final ArrayList<String> order = new ArrayList<String>(featureModel.getNumberOfFeatures());
		for (final Element e : getElements(nodeList)) {
			if (e.hasAttributes()) {
				final NamedNodeMap nodeMap = e.getAttributes();
				for (int i = 0; i < nodeMap.getLength(); i++) {
					final org.w3c.dom.Node node = nodeMap.item(i);
					final String attributeName = node.getNodeName();
					final String attributeValue = node.getNodeValue();
					if (attributeName.equals(USER_DEFINED)) {
						featureModel.setFeatureOrderUserDefined(attributeValue.equals(TRUE));
					} else if (attributeName.equals(NAME)) {
						if (featureModel.getFeature(attributeValue) != null) {
							order.add(attributeValue);
						} else {
							throwError("Feature \"" + attributeValue + "\" does not exists", e);
						}
					} else {
						throwError("Unknown feature order attribute: " + attributeName, e);
					}

				}
			}
			if (e.hasChildNodes()) {
				parseFeatureOrder(e.getChildNodes());
			}
		}
		if (!order.isEmpty()) {
			featureModel.setFeatureOrderList(order);
		}
	}

	/**
	 * Parses the calculations.
	 */
	private void parseCalculations(NodeList nodeList) throws UnsupportedModelException {
		for (final Element e : getElements(nodeList)) {
			if (e.hasAttributes()) {
				final NamedNodeMap nodeMap = e.getAttributes();
				for (int i = 0; i < nodeMap.getLength(); i++) {
					final org.w3c.dom.Node node = nodeMap.item(i);
					final String nodeName = node.getNodeName();
					final boolean value = node.getNodeValue().equals(TRUE);
					if (nodeName.equals(CALCULATE_AUTO)) {
						featureModel.getAnalyser().runCalculationAutomatically = value;
					} else if (nodeName.equals(CALCULATE_CONSTRAINTS)) {
						featureModel.getAnalyser().calculateConstraints = value;
					} else if (nodeName.equals(CALCULATE_REDUNDANT)) {
						featureModel.getAnalyser().calculateRedundantConstraints = value;
					} else if (nodeName.equals(CALCULATE_FEATURES)) {
						featureModel.getAnalyser().calculateFeatures = value;
					} else if (nodeName.equals(CALCULATE_TAUTOLOGY)) {
						featureModel.getAnalyser().calculateTautologyConstraints = value;
					} else {
						throwError("Unknown calculations attribute: " + nodeName, e);
					}

				}
			}
		}
	}

	/**
	 * Throws an error that will be used for error markers
	 *
	 * @param message The error message
	 * @param tempNode The node that causes the error. this node is used for positioning.
	 */
	private void throwError(String message, org.w3c.dom.Node node) throws UnsupportedModelException {
		throw new UnsupportedModelException(message, Integer.parseInt(node.getUserData(PositionalXMLReader.LINE_NUMBER_KEY_NAME).toString()));
	}
}
