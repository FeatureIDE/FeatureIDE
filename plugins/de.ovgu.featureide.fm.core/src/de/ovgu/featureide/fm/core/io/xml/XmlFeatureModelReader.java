/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io.xml;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
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

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Parses a FeatureModel from XML
 * 
 * @author Jens Meinicke
 */
// TODO revise duplicate code
public class XmlFeatureModelReader extends AbstractFeatureModelReader implements XMLFeatureModelTags {

	public XmlFeatureModelReader(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}

	@Override
	protected synchronized void parseInputStream(final InputStream inputStream)
			throws UnsupportedModelException {
		featureModel.reset();
		featureModel.getLayout().showHiddenFeatures(true);
		featureModel.getLayout().verticalLayout(false);
		Document  doc = null;
		try {
			doc = PositionalXMLReader.readXML(inputStream);
		} catch (SAXParseException e) {
			throw new UnsupportedModelException(e.getMessage(), e.getLineNumber());
		} catch (IOException e) {
			FMCorePlugin.getDefault().logError(e);
		} catch (SAXException e) {
			FMCorePlugin.getDefault().logError(e);
		} catch (ParserConfigurationException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		doc.getDocumentElement().normalize();
		NodeList nList = doc.getElementsByTagName(FEATURE_MODEL);
		for (int temp = 0; temp < nList.getLength(); temp++) {
			org.w3c.dom.Node nNode = nList.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				Element eElement = (Element) nNode;
				setFeatureModelAttributes(eElement);
				parseStruct(eElement.getElementsByTagName(STRUCT));
				parseConstraints(eElement.getElementsByTagName(CONSTRAINTS));
				parseCalculations(eElement.getElementsByTagName(CALCULATIONS));
				parseComments(eElement.getElementsByTagName(COMMENTS));
				parseFeatureOrder(eElement.getElementsByTagName(FEATURE_ORDER));
			}
		}
	
		featureModel.handleModelDataLoaded();
	}

	/**
	 * Adds attributes to the feature model
	 */
	private void setFeatureModelAttributes(Element eElement) {
		String algorithm = eElement.getAttribute(CHOSEN_LAYOUT_ALGORITHM);
		if (!algorithm.equals("")) {
			featureModel.getLayout().setLayout(
					Integer.parseInt(algorithm));
		}
		String layout = eElement.getAttribute(HORIZONTAL_LAYOUT);
		if (layout.equals(TRUE)) {
			featureModel.getLayout().verticalLayout(false);
		} else if (layout.equals(FALSE)) {
			featureModel.getLayout().verticalLayout(true);
		}
		String showHidden = eElement.getAttribute(SHOW_HIDDEN_FEATURES);
		if (showHidden.equals(TRUE)) {
			featureModel.getLayout().showHiddenFeatures(true);
		} else if (showHidden.equals(FALSE)) {
			featureModel.getLayout().showHiddenFeatures(false);
		}
	}

	/**
	 * Parse the struct section to add features to the model.
	 * @throws UnsupportedModelException 
	 */
	private void parseStruct(NodeList struct) throws UnsupportedModelException {
		for (int temp = 0; temp < struct.getLength(); temp++) {
			org.w3c.dom.Node nNode = struct.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				Element eElement = (Element) nNode;
				parseFeatures(eElement.getChildNodes(), null);
			}
		}
	}
	
	private void parseFeatures(NodeList nodeList, Feature parent) throws UnsupportedModelException {
		for (int count = 0; count < nodeList.getLength(); count++) {
			org.w3c.dom.Node tempNode = nodeList.item(count);
			if (tempNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				String nodeName = tempNode.getNodeName();
				if (nodeName.equals(DESCRIPTION)) {
					/* case: description */
					String nodeValue = tempNode.getFirstChild().getNodeValue();
					parent.setDescription(nodeValue);
					continue;
				}
				boolean mandatory = false;
				boolean _abstract = false;
				boolean hidden = false;
				String name = "";
				FMPoint featureLocation = null;
				if (tempNode.hasAttributes()) {
					NamedNodeMap nodeMap = tempNode.getAttributes();
					for (int i = 0; i < nodeMap.getLength(); i++) {
						org.w3c.dom.Node node = nodeMap.item(i);
						String attributeName = node.getNodeName();
						String attributeValue = node.getNodeValue();
						if (attributeName.equals(ABSTRACT)) {
							_abstract = attributeValue.equals(TRUE);
						} else if (attributeName.equals(MANDATORY)) {
							mandatory = attributeValue.equals(TRUE);
						} else if (attributeName.equals(NAME)) {
							name = attributeValue;
						} else if (attributeName.equals(HIDDEN)) {
							hidden = attributeValue.equals(TRUE);
						} else if (attributeName.equals(COORDINATES)) {
							String subStringX = attributeValue.substring(0, attributeValue.indexOf(", "));
							String subStringY = attributeValue.substring(attributeValue.indexOf(", ")+2);
							try {
								featureLocation = new FMPoint(Integer.parseInt (subStringX),
											Integer.parseInt (subStringY));
							} catch (NumberFormatException e) {
								throwError(e.getMessage() + "is no valid Integer Value", tempNode);
							}
						} else {
							throwError("Unknown feature attribute: " + attributeName, tempNode);
						}

					}
				}
				if (featureModel.getFeatureTable().containsKey(name)) {
					throwError("Duplicate entry for feature: " + name, tempNode);
				}
				if (!featureModel.getFMComposerExtension().isValidFeatureName(name)) {
					throwError(name + "is no valid feature name", tempNode);
				}
				Feature f = new Feature(featureModel, name);
				f.setMandatory(true);
				if (nodeName.equals(AND)) {
					f.setAnd();
				} else if (nodeName.equals(ALT)) {
					f.setAlternative();
				} else if (nodeName.equals(OR)) {
					f.setOr();
				} else if (nodeName.equals(FEATURE)) {
					
				} else {
					throwError("Unknown feature type: " + nodeName, tempNode);
				}
				f.setAbstract(_abstract);
				f.setMandatory(mandatory);
				f.setHidden(hidden);
				if (featureLocation != null) {
					f.setNewLocation(featureLocation);
				}
				featureModel.addFeature(f);
				if (parent == null) {
					featureModel.setRoot(f);
				} else {
					parent.addChild(f);
				}
				if (tempNode.hasChildNodes()) {
					parseFeatures(tempNode.getChildNodes(), f);
				}
			}
		}
	}

	/**
	 * Parses the constraint section.
	 * @throws UnsupportedModelException 
	 * 
	 */
	private void parseConstraints(NodeList nodeList) throws UnsupportedModelException {
		for (int temp = 0; temp < nodeList.getLength(); temp++) {
			org.w3c.dom.Node nNode = nodeList.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				Element eElement = (Element) nNode;
				parseConstraints2(eElement.getChildNodes());
			}
		}
	}
	
	private void parseConstraints2(NodeList nodeList) throws UnsupportedModelException {
		for (int temp = 0; temp < nodeList.getLength(); temp++) {
			org.w3c.dom.Node nNode = nodeList.item(temp);
			if (nNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				Element eElement = (Element) nNode;
				String nodeName = nNode.getNodeName();
				if (nodeName.equals(RULE)) {
					Constraint c = new Constraint(featureModel, (Node) parseConstraints3(eElement.getChildNodes()).getFirst());
					if (eElement.hasAttributes()) {
						NamedNodeMap nodeMap = eElement.getAttributes();
						for (int i = 0; i < nodeMap.getLength(); i++) {
							org.w3c.dom.Node node = nodeMap.item(i);
							String attributeName = node.getNodeName();
							String attributeValue = node.getNodeValue();
							if (attributeName.equals(COORDINATES)) {
								String subStringX = attributeValue.substring(0, attributeValue.indexOf(", "));
								String subStringY = attributeValue.substring(attributeValue.indexOf(", ")+2);
								try {
									c.setLocation(new FMPoint(Integer.parseInt (subStringX),
												Integer.parseInt (subStringY)));
								} catch (NumberFormatException e) {
									throwError(e.getMessage() + "is no valid Integer Value", nNode);
								}
							} else {
								throwError("Unknown constraint attribute: " + attributeName, node);
							}
						}
					}
					featureModel.addConstraint(c);
				} else {
					throwError("Unknown constraint node: " + nodeName, nNode);
				}
			}
		}
	}

	private LinkedList<Node> parseConstraints3(NodeList nodeList) throws UnsupportedModelException {
		LinkedList<Node> nodes = new LinkedList<Node>();
		for (int count = 0; count < nodeList.getLength(); count++) {
			org.w3c.dom.Node tempNode = nodeList.item(count);
			if (tempNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				String nodeName = tempNode.getNodeName();
				if (nodeName.equals(DISJ)) {
					nodes.add( new Or(parseConstraints3(tempNode.getChildNodes())));
				} else if (nodeName.equals(CONJ)) {
					nodes.add( new And(parseConstraints3(tempNode.getChildNodes())));
				} else if (nodeName.equals(EQ)) {
					LinkedList<Node> children = parseConstraints3(tempNode.getChildNodes());
					nodes.add( new Equals(children.get(0), children.get(1)));
				} else if (nodeName.equals(IMP)) {
					LinkedList<Node> children = parseConstraints3(tempNode.getChildNodes());
					nodes.add( new Implies(children.get(0), children.get(1)));
				} else if (nodeName.equals(NOT)) {
					nodes.add( new Not((parseConstraints3(tempNode.getChildNodes())).getFirst()));
				} else if (nodeName.equals(ATMOST1)) {
					nodes.add( new AtMost(1, parseConstraints3(tempNode.getChildNodes())));
				} else if (nodeName.equals(VAR)) {
					String feature = tempNode.getTextContent();
					if (featureModel.getFeatureTable().containsKey(feature)) {
						nodes.add(new Literal(feature));
					} else {
						throwError("Feature \"" + feature + "\" does not exists", tempNode);
					}
				} else {
					throwError("Unknown constraint type: " + nodeName, tempNode);
				}
			}
		}
		return nodes;
	}

	/**
	 * Parses the comment section.
	 * @throws UnsupportedModelException 
	 * 
	 */
	private void parseComments(NodeList nodeList) throws UnsupportedModelException {
		for (int count = 0; count < nodeList.getLength(); count++) {
			org.w3c.dom.Node tempNode = nodeList.item(count);
			if (tempNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				if (tempNode.hasChildNodes()) {
					parseComments2(tempNode.getChildNodes());
				}
			}
		}
	}

	private void parseComments2(NodeList nodeList) throws UnsupportedModelException {
		for (int count = 0; count < nodeList.getLength(); count++) {
			org.w3c.dom.Node tempNode = nodeList.item(count);
			if (tempNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				if (tempNode.getNodeName().equals(C)) {
					featureModel.addComment(tempNode.getTextContent());
				} else {
					throwError("Unknown comment attribute: " + tempNode.getNodeName(), tempNode);
				}
			}
		}
	}

	/**
	 * Parses the feature order section.
	 * @throws UnsupportedModelException 
	 * 
	 */
	private void parseFeatureOrder(NodeList nodeList) throws UnsupportedModelException {
		ArrayList<String> order = new ArrayList<String>(featureModel.getFeatureTable().size());
		for (int count = 0; count < nodeList.getLength(); count++) {
			org.w3c.dom.Node tempNode = nodeList.item(count);
			if (tempNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				if (tempNode.hasAttributes()) {
					NamedNodeMap nodeMap = tempNode.getAttributes();
					for (int i = 0; i < nodeMap.getLength(); i++) {
						org.w3c.dom.Node node = nodeMap.item(i);
						String attributeName = node.getNodeName();
						String attributeValue = node.getNodeValue();
						if (attributeName.equals(USER_DEFINED)) {
							featureModel.setFeatureOrderUserDefined(attributeValue.equals(TRUE));
						} else if (attributeName.equals(NAME)){
							if (featureModel.getFeatureTable().containsKey(attributeValue)) {
								order.add(attributeValue);
							} else {
								throwError("Feature \"" + attributeValue + "\" does not exists", tempNode);
							}
						} else {
							throwError("Unknown feature order attribute: " + attributeName, tempNode);
						}

					}
				}
				if (tempNode.hasChildNodes()) {
					parseFeatureOrder(tempNode.getChildNodes());
				}
			}
		}
		if (!order.isEmpty()) {
			featureModel.setFeatureOrderList(order);
		}
	}

	/**
	 * Parses the calculations.
	 * @throws UnsupportedModelException 
	 * 
	 */
	private void parseCalculations(NodeList nodeList) throws UnsupportedModelException {
		for (int count = 0; count < nodeList.getLength(); count++) {
			org.w3c.dom.Node tempNode = nodeList.item(count);
			if (tempNode.getNodeType() == org.w3c.dom.Node.ELEMENT_NODE) {
				if (tempNode.hasAttributes()) {
					NamedNodeMap nodeMap = tempNode.getAttributes();
					for (int i = 0; i < nodeMap.getLength(); i++) {
						org.w3c.dom.Node node = nodeMap.item(i);
						String nodeName = node.getNodeName();
						boolean value = node.getNodeValue().equals(TRUE);
						if (nodeName.equals(CALCULATE_AUTO)) {
							featureModel.runCalculationAutomatically = value;
						} else if (nodeName.equals(CALCULATE_CONSTRAINTS)) {
							featureModel.calculateConstraints = value;
						} else if (nodeName.equals(CALCULATE_REDUNDANT)) {
							featureModel.calculateRedundantConstraints = value;
						} else if (nodeName.equals(CALCULATE_FEATURES)) {
							featureModel.calculateFeatures = value;
						} else {
							throwError("Unknown calculations attribute: " + nodeName, tempNode);
						}

					}
				}
			}
		}
	}
	
	
	/**
	 * Throws an error that will be used for error markers
	 * @param message The error message
	 * @param tempNode The node that causes the error. this node is used for positioning. 
	 */
	private void throwError(String message, org.w3c.dom.Node node) throws UnsupportedModelException {
		throw new UnsupportedModelException(message, 
				Integer.parseInt (node.getUserData(PositionalXMLReader.LINE_NUMBER_KEY_NAME).toString()));
	}
}