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

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;

import org.prop4j.And;
import org.prop4j.AtMost;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Not;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.w3c.dom.Text;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Entry;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Type;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlPropertyLoader.PropertiesParser;

/**
 * Reads / Writes a feature model in the FeatureIDE XML format
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 * @author Sebastian Krieter
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public class XmlFeatureModelFormat extends AXMLFormat<IFeatureModel> implements IFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + XmlFeatureModelFormat.class.getSimpleName();

	private static final Pattern CONTENT_REGEX = Pattern.compile("\\A\\s*(<[?]xml\\s.*[?]>\\s*)?<featureModel[\\s>]");

	private IFeatureModelFactory factory;

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		object.reset();

		factory = FMFactoryManager.getFactory(object);

		final Collection<PropertiesParser> customProperties = new ArrayList<>();

		for (final Element e : getElements(doc.getElementsByTagName(FEATURE_MODEL))) {
			parseStruct(e.getElementsByTagName(STRUCT));
			parseConstraints(e.getElementsByTagName(CONSTRAINTS));
			parseCalculations(e.getElementsByTagName(CALCULATIONS));
			parseComments(e.getElementsByTagName(COMMENTS));
			parseFeatureOrder(e.getElementsByTagName(FEATURE_ORDER));

			final XmlPropertyLoader propertyLoader = new XmlPropertyLoader(e.getElementsByTagName(PROPERTIES));
			customProperties.addAll(propertyLoader.parseProperties());
		}

		if (object.getStructure().getRoot() == null) {
			throw new UnsupportedModelException(WRONG_SYNTAX, 1);
		}

		importCustomProperties(customProperties, object);
	}

	@Override
	protected void writeDocument(Document doc) {
		final Element root = doc.createElement(FEATURE_MODEL);
		final Element struct = doc.createElement(STRUCT);
		final Element properties = doc.createElement(PROPERTIES);
		final Element constraints = doc.createElement(CONSTRAINTS);
		final Element calculations = doc.createElement(CALCULATIONS);
		final Element comments = doc.createElement(COMMENTS);
		final Element order = doc.createElement(FEATURE_ORDER);

		doc.appendChild(root);
		root.appendChild(properties);
		createXmlPropertiesPart(doc, properties, object);

		root.appendChild(struct);
		createXmlDocRec(doc, struct, FeatureUtils.getRoot(object));

		root.appendChild(constraints);
		for (final IConstraint constraint : object.getConstraints()) {
			Element rule;
			rule = doc.createElement(RULE);

			constraints.appendChild(rule);
			addDescription(doc, constraint, rule);
			createPropositionalConstraints(doc, rule, constraint.getNode());
		}

		root.appendChild(calculations);
		calculations.setAttribute(CALCULATE_AUTO, "" + object.getAnalyser().runCalculationAutomatically);
		calculations.setAttribute(CALCULATE_FEATURES, "" + object.getAnalyser().calculateFeatures);
		calculations.setAttribute(CALCULATE_CONSTRAINTS, "" + object.getAnalyser().calculateConstraints);
		calculations.setAttribute(CALCULATE_REDUNDANT, "" + object.getAnalyser().calculateRedundantConstraints);
		calculations.setAttribute(CALCULATE_TAUTOLOGY, "" + object.getAnalyser().calculateTautologyConstraints);

		root.appendChild(comments);
		for (final String comment : object.getProperty().getComments()) {
			final Element c = doc.createElement(C);
			comments.appendChild(c);
			final Text text = doc.createTextNode(comment);
			c.appendChild(text);
		}
		order.setAttribute(USER_DEFINED, Boolean.toString(object.isFeatureOrderUserDefined()));
		root.appendChild(order);

		if (object.isFeatureOrderUserDefined()) {
			Collection<String> featureOrderList = object.getFeatureOrderList();

			if (featureOrderList.isEmpty()) {
				featureOrderList = FeatureUtils.extractConcreteFeaturesAsStringList(object);
			}

			for (final String featureName : featureOrderList) {
				final Element feature = doc.createElement(FEATURE);
				feature.setAttribute(NAME, featureName);
				order.appendChild(feature);
			}
		}
	}

	private Node createFeaturePropertyContainerNode(Document doc, String featureName, Set<Entry<String, Type, Object>> propertyEntries) {
		final Element result = doc.createElement(FEATURE);
		result.setAttribute(NAME, featureName);
		for (final Entry<String, Type, Object> entry : propertyEntries) {
			result.appendChild(createPropertyEntriesNode(doc, entry));
		}
		return result;
	}

	private Node createPropertyEntriesNode(Document doc, Entry<String, Type, Object> entry) {
		final Element propertyElement = doc.createElement(XmlPropertyLoader.PROPERTY);
		propertyElement.setAttribute(XmlPropertyLoader.KEY, entry.getKey());
		propertyElement.setAttribute(XmlPropertyLoader.VALUE, entry.getValue().toString());
		propertyElement.setAttribute(XmlPropertyLoader.TYPE, entry.getType().toString());
		return propertyElement;
	}

	/**
	 * Inserts the tags concerning propositional constraints into the DOM document representation
	 *
	 * @param doc
	 * @param FeatMod Parent node for the propositional nodes
	 */
	private void createPropositionalConstraints(Document doc, Element xmlNode, org.prop4j.Node node) {
		if (node == null) {
			return;
		}

		final Element op;
		if (node instanceof Literal) {
			final Literal literal = (Literal) node;
			if (!literal.positive) {
				final Element opNot = doc.createElement(NOT);
				xmlNode.appendChild(opNot);
				xmlNode = opNot;
			}
			op = doc.createElement(VAR);
			op.appendChild(doc.createTextNode(String.valueOf(literal.var)));
			xmlNode.appendChild(op);
			return;
		} else if (node instanceof Or) {
			op = doc.createElement(DISJ);
		} else if (node instanceof Equals) {
			op = doc.createElement(EQ);
		} else if (node instanceof Implies) {
			op = doc.createElement(IMP);
		} else if (node instanceof And) {
			op = doc.createElement(CONJ);
		} else if (node instanceof Not) {
			op = doc.createElement(NOT);
		} else if (node instanceof AtMost) {
			op = doc.createElement(ATMOST1);
		} else {
			op = doc.createElement(UNKNOWN);
		}
		xmlNode.appendChild(op);

		for (final org.prop4j.Node child : node.getChildren()) {
			createPropositionalConstraints(doc, op, child);
		}
	}

	/**
	 * Creates document based on feature model step by step
	 *
	 * @param doc document to write
	 * @param node parent node
	 * @param feat current feature
	 */
	private void createXmlDocRec(Document doc, Element node, IFeature feat) {
		if (feat == null) {
			return;
		}

		final List<IFeature> children = FeatureUtils.convertToFeatureList(feat.getStructure().getChildren());

		final Element fnod;
		if (children.isEmpty()) {
			fnod = doc.createElement(FEATURE);
			addDescription(doc, feat, fnod);
			writeAttributes(node, fnod, feat);
		} else {
			if (feat.getStructure().isAnd()) {
				fnod = doc.createElement(AND);
			} else if (feat.getStructure().isOr()) {
				fnod = doc.createElement(OR);
			} else if (feat.getStructure().isAlternative()) {
				fnod = doc.createElement(ALT);
			} else {
				fnod = doc.createElement(UNKNOWN);// Logger.logInfo("creatXMlDockRec: Unexpected error!");
			}

			addDescription(doc, feat, fnod);
			writeAttributes(node, fnod, feat);

			for (final IFeature feature : children) {
				createXmlDocRec(doc, fnod, feature);
			}

		}

	}

	protected void addDescription(Document doc, IFeature feat, Element fnod) {
		final String description = feat.getProperty().getDescription();
		if ((description != null) && !description.trim().isEmpty()) {
			final Element descr = doc.createElement(DESCRIPTION);
			descr.setTextContent("\n" + description.replace("\r", "") + "\n");
			fnod.appendChild(descr);
		}
	}

	protected void addDescription(Document doc, IConstraint constraint, Element fnod) {
		final String description = constraint.getDescription();
		if ((description != null) && !description.trim().isEmpty()) {
			final Element descr = doc.createElement(DESCRIPTION);
			descr.setTextContent("\n" + description.replace("\r", "") + "\n");
			fnod.appendChild(descr);
		}
	}

	private void createXmlPropertiesPart(Document doc, Element propertiesNode, IFeatureModel featureModel) {

		if ((featureModel == null) || (propertiesNode == null)) {
			throw new RuntimeException();
		}

		// Store per-feature properties
		for (final IFeature feature : featureModel.getFeatures()) {
			final String featureName = feature.getName();
			final Set<Entry<String, Type, Object>> propertyEntries = feature.getCustomProperties().entrySet();
			if (!propertyEntries.isEmpty()) {
				propertiesNode.appendChild(createFeaturePropertyContainerNode(doc, featureName, propertyEntries));
			}
		}

		// TODO: Add here other property container, e.g., feature model
		// ...
	}

	private void importCustomProperties(Collection<PropertiesParser> customProperties, IFeatureModel object) {
		for (final PropertiesParser parser : customProperties) {
			switch (parser.getType()) {
			case FEATURE_PROPERTIES_PARSER: {
				for (final String featureName : parser.getIdentifier()) {
					object.getFeature(featureName).getCustomProperties().setEntrySet(parser.getPropertyEntries(featureName));
				}
				break;
			}
			default:
				throw new UnsupportedOperationException("Unkown property container parser type " + parser.getType());
			}
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
						object.getAnalyser().runCalculationAutomatically = value;
					} else if (nodeName.equals(CALCULATE_CONSTRAINTS)) {
						object.getAnalyser().calculateConstraints = value;
					} else if (nodeName.equals(CALCULATE_REDUNDANT)) {
						object.getAnalyser().calculateRedundantConstraints = value;
					} else if (nodeName.equals(CALCULATE_FEATURES)) {
						object.getAnalyser().calculateFeatures = value;
					} else if (nodeName.equals(CALCULATE_TAUTOLOGY)) {
						object.getAnalyser().calculateTautologyConstraints = value;
					} else {
						throwError("Unknown calculations attribute: " + nodeName, e);
					}

				}
			}
		}
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
				object.getProperty().addComment(e.getTextContent());
			} else {
				throwError("Unknown comment attribute: " + e.getNodeName(), e);
			}
		}
	}

	/**
	 * Parses the description of a constraint
	 *
	 * @param constraint Output parameter: the constraint will have the description set
	 * @param parentOfDescription The parent tag of the description tag
	 */
	private void parseConstraintDescription(IConstraint constraint, final Element parentOfDescription) {
		for (final Element childOfRule : getElements(parentOfDescription.getChildNodes())) {
			if (childOfRule.getNodeName().equals(DESCRIPTION)) {
				String description = childOfRule.getTextContent();

				if ((description != null) && !description.isEmpty()) {
					description = description.replace("\t", "");
					description = description.trim();
				}

				constraint.setDescription(description);
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
					final IConstraint c = factory.createConstraint(object, parseConstraints2(child.getChildNodes()).getFirst());
					if (child.hasAttributes()) {
						final NamedNodeMap nodeMap = child.getAttributes();
						for (int i = 0; i < nodeMap.getLength(); i++) {
							final org.w3c.dom.Node node = nodeMap.item(i);
							final String attributeName = node.getNodeName();
							if (attributeName.equals(COORDINATES)) {
								// Legacy case, for backwards compatibility
							} else {
								throwError("Unknown constraint attribute: " + attributeName, node);
							}
						}
					}
					parseConstraintDescription(c, child);
					object.addConstraint(c);
				} else {
					throwError("Unknown constraint node: " + nodeName, child);
				}
			}
		}
	}

	private LinkedList<org.prop4j.Node> parseConstraints2(NodeList nodeList) throws UnsupportedModelException {
		final LinkedList<org.prop4j.Node> nodes = new LinkedList<>();
		LinkedList<org.prop4j.Node> children;
		for (final Element e : getElements(nodeList)) {
			final String nodeName = e.getNodeName();
			if (nodeName.equals(DISJ)) {
				nodes.add(new Or(parseConstraints2(e.getChildNodes())));
			} else if (nodeName.equals(CONJ)) {
				nodes.add(new And(parseConstraints2(e.getChildNodes())));
			} else if (nodeName.equals(EQ)) {
				children = parseConstraints2(e.getChildNodes());
				nodes.add(new Equals(children.get(0), children.get(1)));
			} else if (nodeName.equals(IMP)) {
				children = parseConstraints2(e.getChildNodes());
				nodes.add(new Implies(children.get(0), children.get(1)));
			} else if (nodeName.equals(NOT)) {
				nodes.add(new Not((parseConstraints2(e.getChildNodes())).getFirst()));
			} else if (nodeName.equals(ATMOST1)) {
				nodes.add(new AtMost(1, parseConstraints2(e.getChildNodes())));
			} else if (nodeName.equals(VAR)) {
				final String featureName = e.getTextContent();
				if (object.getFeature(featureName) != null) {
					nodes.add(new Literal(featureName));
				} else {
					throwError("Feature \"" + featureName + "\" does not exists", e);
				}
			} else if (nodeName.equals(DESCRIPTION)) {
				/**
				 * The method should return without adding any nodes, and traverse deeper into the tree, because description, has no children just return the
				 * current list. The actual readout of the description happens at a different point.
				 */
			} else {
				throwError("Unknown constraint type: " + nodeName, e);
			}
		}
		return nodes;
	}

	/**
	 * Parses the feature order section.
	 */
	private void parseFeatureOrder(NodeList nodeList) throws UnsupportedModelException {
		final ArrayList<String> order = new ArrayList<>(object.getNumberOfFeatures());
		for (final Element e : getElements(nodeList)) {
			if (e.hasAttributes()) {
				final NamedNodeMap nodeMap = e.getAttributes();
				for (int i = 0; i < nodeMap.getLength(); i++) {
					final org.w3c.dom.Node node = nodeMap.item(i);
					final String attributeName = node.getNodeName();
					final String attributeValue = node.getNodeValue();
					if (attributeName.equals(USER_DEFINED)) {
						object.setFeatureOrderUserDefined(attributeValue.equals(TRUE));
					} else if (attributeName.equals(NAME)) {
						if (object.getFeature(attributeValue) != null) {
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
			object.setFeatureOrderList(order);
		}
	}

	private void parseFeatures(NodeList nodeList, IFeature parent) throws UnsupportedModelException {
		for (final Element e : getElements(nodeList)) {
			final String nodeName = e.getNodeName();
			if (nodeName.equals(DESCRIPTION)) {
				/* case: description */
				String nodeValue = e.getFirstChild().getNodeValue();
				if ((nodeValue != null) && !nodeValue.isEmpty()) {
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
			// FMPoint featureLocation = null;
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
						// Legacy case, for backwards compatibility
					} else {
						throwError("Unknown feature attribute: " + attributeName, e);
					}

				}
			}

			if (object.getFeature(name) != null) {
				throwError("Duplicate entry for feature: " + name, e);
			}
			// TODO Consider feature name validity in all readers
			// if (!object.getFMComposerExtension().isValidFeatureName(name)) {
			// throwError(name + IS_NO_VALID_FEATURE_NAME, e);
			// }
			final IFeature f = factory.createFeature(object, name);
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

			object.addFeature(f);
			if (parent == null) {
				object.getStructure().setRoot(f.getStructure());
			} else {
				parent.getStructure().addChild(f.getStructure());
			}
			if (e.hasChildNodes()) {
				parseFeatures(e.getChildNodes(), f);
			}
		}

	}

	/**
	 * Parse the struct section to add features to the model.
	 */
	private void parseStruct(NodeList struct) throws UnsupportedModelException {
		for (final Element e : getElements(struct)) {
			parseFeatures(e.getChildNodes(), null);
		}
	}

	/**
	 * Throws an error that will be used for error markers
	 *
	 * @param message The error message
	 * @param tempNode The node that causes the error. this node is used for positioning.
	 */
	private void throwError(String message, org.w3c.dom.Node node) throws UnsupportedModelException {
		throw new UnsupportedModelException(message, Integer.parseInt(node.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME).toString()));
	}

	// TODO implement warnings
	@SuppressWarnings("unused")
	private void throwWarning(String message, org.w3c.dom.Node node) throws UnsupportedModelException {
		throw new UnsupportedModelException(message, Integer.parseInt(node.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME).toString()));
	}

	private void writeAttributes(Element node, Element fnod, IFeature feat) {
		fnod.setAttribute(NAME, feat.getName());
		if (feat.getStructure().isHidden()) {
			fnod.setAttribute(HIDDEN, TRUE);
		}
		if (feat.getStructure().isMandatory()) {
			if ((feat.getStructure().getParent() != null) && feat.getStructure().getParent().isAnd()) {
				fnod.setAttribute(MANDATORY, TRUE);
			} else if (feat.getStructure().getParent() == null) {
				fnod.setAttribute(MANDATORY, TRUE);
			}
		}
		if (feat.getStructure().isAbstract()) {
			fnod.setAttribute(ABSTRACT, TRUE);
		}

		node.appendChild(fnod);
	}

	@Override
	public XmlFeatureModelFormat getInstance() {
		return new XmlFeatureModelFormat();
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return supportsRead() && CONTENT_REGEX.matcher(content).find();
	}

	@Override
	public boolean supportsContent(LazyReader reader) {
		return super.supportsContent(reader, CONTENT_REGEX);
	}

	@Override
	public String getName() {
		return "FeatureIDE";
	}

}
