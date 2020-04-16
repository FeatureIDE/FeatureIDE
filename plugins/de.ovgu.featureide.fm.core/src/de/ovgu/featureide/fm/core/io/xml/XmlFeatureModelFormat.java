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

import static de.ovgu.featureide.fm.core.localization.StringTable.ABSTRACT;
import static de.ovgu.featureide.fm.core.localization.StringTable.COMMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDDEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.MANDATORY;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOT;
import static de.ovgu.featureide.fm.core.localization.StringTable.WRONG_SYNTAX;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
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
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Entry;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IFeatureNameValidator;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

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

	protected IFeatureModelFactory factory;
	protected IFeatureNameValidator validator;

	protected final List<Problem> localProblems = new ArrayList<>();

	public XmlFeatureModelFormat() {}

	protected XmlFeatureModelFormat(XmlFeatureModelFormat oldFormat) {
		validator = oldFormat.validator;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		object.reset();

		factory = FMFactoryManager.getInstance().getFactory(object);

		for (final Element e : getElement(doc, FEATURE_MODEL, false)) {
			parseStruct(getElement(e, STRUCT, false));
			parseConstraints(getElement(e, CONSTRAINTS, true));
			parseComments(getElement(e, COMMENTS, true));
			parseFeatureOrder(getElement(e, FEATURE_ORDER, true));
			parseCalculations(getElement(e, CALCULATIONS, true));
			parseFeatureModelProperties(getElement(e, PROPERTIES, true));
		}

		if (object.getStructure().getRoot() == null) {
			throw new UnsupportedModelException(WRONG_SYNTAX, 1);
		}

		warnings.addAll(localProblems);
	}

	@Override
	protected void writeDocument(Document doc) {
		final Element root = doc.createElement(FEATURE_MODEL);
		doc.appendChild(root);

		writeProperties(doc, root);
		writeFeatures(doc, root);
		writeConstraints(doc, root);
		writeComments(doc, root);
		writeFeatureOrder(doc, root);
	}

	protected void writeProperties(Document doc, final Element root) {
		if (!object.getProperty().getProperties().isEmpty()) {
			final Element properties = doc.createElement(PROPERTIES);
			root.appendChild(properties);
			addProperties(doc, object.getProperty(), properties);
		}
	}

	protected void writeFeatures(Document doc, final Element root) {
		final Element struct = doc.createElement(STRUCT);
		root.appendChild(struct);
		writeFeatureTreeRec(doc, struct, FeatureUtils.getRoot(object));
	}

	protected void writeConstraints(Document doc, final Element root) {
		if (!object.getConstraints().isEmpty()) {
			final Element constraints = doc.createElement(CONSTRAINTS);
			root.appendChild(constraints);
			for (final IConstraint constraint : object.getConstraints()) {
				Element rule;
				rule = doc.createElement(RULE);

				constraints.appendChild(rule);
				addDescription(doc, constraint.getDescription(), rule);
				addProperties(doc, constraint.getCustomProperties(), rule);
				createPropositionalConstraints(doc, rule, constraint.getNode());
			}
		}
	}

	protected void writeComments(Document doc, final Element root) {
		if (!object.getProperty().getComments().isEmpty()) {
			final Element comments = doc.createElement(COMMENTS);
			root.appendChild(comments);
			for (final String comment : object.getProperty().getComments()) {
				final Element c = doc.createElement(C);
				comments.appendChild(c);
				final Text text = doc.createTextNode(comment);
				c.appendChild(text);
			}
		}
	}

	protected void writeFeatureOrder(Document doc, final Element root) {
		if (object.isFeatureOrderUserDefined()) {
			final Element order = doc.createElement(FEATURE_ORDER);
			order.setAttribute(USER_DEFINED, Boolean.toString(object.isFeatureOrderUserDefined()));
			root.appendChild(order);
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

	/**
	 * Inserts the tags concerning propositional constraints into the DOM document representation
	 *
	 * @param doc
	 * @param node Parent node for the propositional nodes
	 */
	protected void createPropositionalConstraints(Document doc, Element xmlNode, org.prop4j.Node node) {
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
	protected void writeFeatureTreeRec(Document doc, Element node, IFeature feat) {
		if (feat == null) {
			return;
		}

		final List<IFeature> children = FeatureUtils.convertToFeatureList(feat.getStructure().getChildren());

		final Element fnod;
		if (children.isEmpty()) {
			fnod = doc.createElement(FEATURE);
			writeFeatureProperties(doc, node, feat, fnod);
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

			writeFeatureProperties(doc, node, feat, fnod);

			for (final IFeature feature : children) {
				writeFeatureTreeRec(doc, fnod, feature);
			}

		}

	}

	protected void writeFeatureProperties(Document doc, Element node, IFeature feat, final Element fnod) {
		addDescription(doc, feat.getProperty().getDescription(), fnod);
		addProperties(doc, feat.getCustomProperties(), fnod);
		writeAttributes(node, fnod, feat);
	}

	protected void addDescription(Document doc, String description, Element fnod) {
		if ((description != null) && !description.trim().isEmpty()) {
			final Element descr = doc.createElement(DESCRIPTION);
			descr.setTextContent(description);
			fnod.appendChild(descr);
		}
	}

	protected void addProperties(Document doc, IPropertyContainer properties, Element fnod) {
		for (final Entry property : properties.getProperties()) {
			if (property.getValue() != null) {
				final Element propNode;
				if (GRAPHICS.equals(property.getType())) {
					propNode = doc.createElement(GRAPHICS);
				} else if (CALCULATIONS.equals(property.getType())) {
					propNode = doc.createElement(CALCULATIONS);
				} else {
					propNode = doc.createElement(PROPERTY);
					propNode.setAttribute(TYPE, property.getType());
				}
				propNode.setAttribute(KEY, property.getKey());
				propNode.setAttribute(VALUE, property.getValue());
				fnod.appendChild(propNode);
			}
		}
	}

	/**
	 * Parses the comment section.
	 */
	protected void parseComments(List<Element> elements) throws UnsupportedModelException {
		for (final Element e : elements) {
			if (e.hasChildNodes()) {
				for (final Element e1 : getElements(e.getChildNodes())) {
					if (e1.getNodeName().equals(C)) {
						object.getProperty().addComment(e1.getTextContent());
					} else {
						throwWarning("Unknown comment attribute: " + e1.getNodeName(), e1);
					}
				}
			}
		}
	}

	/**
	 * Parses the constraint section.
	 */
	protected void parseConstraints(List<Element> elements) throws UnsupportedModelException {
		for (final Element e : elements) {
			for (final Element child : getElements(e.getChildNodes())) {
				final String nodeName = child.getNodeName();
				if (nodeName.equals(RULE)) {
					final IConstraint constraint = factory.createConstraint(object, null);
					final LinkedList<org.prop4j.Node> constraintNodeList = parseConstraintNode(child.getChildNodes(), constraint);
					if (constraintNodeList.isEmpty()) {
						throwWarning("Missing elements", e);
					} else if (constraintNodeList.size() > 1) {
						throwWarning("Too many elements", e);
					} else {
						constraint.setNode(constraintNodeList.getFirst());
						if (child.hasAttributes()) {
							final NamedNodeMap nodeMap = child.getAttributes();
							for (int i = 0; i < nodeMap.getLength(); i++) {
								final org.w3c.dom.Node node = nodeMap.item(i);
								final String attributeName = node.getNodeName();
								if (attributeName.equals(COORDINATES)) {
									// Legacy case, for backwards compatibility
								} else {
									throwWarning("Unknown constraint attribute: " + attributeName, node);
								}
							}
						}
						object.addConstraint(constraint);
					}
				} else {
					throwWarning("Unknown constraint node: " + nodeName, child);
				}
			}
		}
	}

	protected LinkedList<org.prop4j.Node> parseConstraintNode(NodeList nodeList, IConstraint parent) throws UnsupportedModelException {
		final LinkedList<org.prop4j.Node> nodes = new LinkedList<>();
		LinkedList<org.prop4j.Node> children;
		for (final Element e : getElements(nodeList)) {
			final String nodeName = e.getNodeName();
			switch (nodeName) {
			case DESCRIPTION:
				if (parent != null) {
					parent.setDescription(getDescription(e));
				} else {
					throwWarning("Misplaced description element", e);
				}
				break;
			case GRAPHICS:
				if (parent != null) {
					parseProperty(parent.getCustomProperties(), e, GRAPHICS);
				} else {
					throwWarning("Misplaced graphics element", e);
				}
				break;
			case PROPERTY:
				if (parent != null) {
					parseProperty(parent.getCustomProperties(), e, null);
				} else {
					throwWarning("Misplaced property element", e);
				}
				break;
			case DISJ:
				nodes.add(new Or(parseConstraintNode(e.getChildNodes(), null)));
				break;
			case CONJ:
				nodes.add(new And(parseConstraintNode(e.getChildNodes(), null)));
				break;
			case EQ:
				children = parseConstraintNode(e.getChildNodes(), null);
				nodes.add(new Equals(children.get(0), children.get(1)));
				break;
			case IMP:
				children = parseConstraintNode(e.getChildNodes(), null);
				nodes.add(new Implies(children.get(0), children.get(1)));
				break;
			case NOT:
				nodes.add(new Not((parseConstraintNode(e.getChildNodes(), null)).getFirst()));
				break;
			case ATMOST1:
				nodes.add(new AtMost(1, parseConstraintNode(e.getChildNodes(), null)));
				break;
			case VAR:
				final String featureName = e.getTextContent();
				if (object.getFeature(featureName) != null) {
					nodes.add(new Literal(featureName));
				} else {
					throwError("Feature \"" + featureName + "\" does not exists", e);
				}
				break;
			default:
				throwWarning("Unknown constraint type: " + nodeName, e);
			}
		}
		return nodes;
	}

	protected String getDescription(final Node e) {
		String description = e.getTextContent();
		// NOTE: THe following code is used for backwards compatibility. It replaces spaces and tabs that were added to the XML for indentation, but don't
		// belong to the actual description.
		if (description != null) {
			description = description.replaceAll("(\r\n|\r|\n)\\s*", "\n").replaceAll("\\A\n|\n\\Z", "");
		}
		return description;
	}

	/**
	 * Parses the feature order section.
	 */
	protected void parseFeatureOrder(List<Element> elements) throws UnsupportedModelException {
		final ArrayList<String> order = new ArrayList<>(object.getNumberOfFeatures());
		for (final Element e : elements) {
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
				parseFeatureOrder(getElements(e.getChildNodes()));
			}
		}
		if (!order.isEmpty()) {
			object.setFeatureOrderList(order);
		}
	}

	protected void parseFeatures(NodeList nodeList, IFeature parent) throws UnsupportedModelException {
		for (final Element e : getElements(nodeList)) {
			final String nodeName = e.getNodeName();
			switch (nodeName) {
			case DESCRIPTION:
				parseDescription(parent, e);
				break;
			case GRAPHICS:
				parseProperty(parent.getCustomProperties(), e, GRAPHICS);
				break;
			case PROPERTY:
				parseProperty(parent.getCustomProperties(), e, null);
				break;
			case AND:
			case OR:
			case ALT:
			case FEATURE:
				parseFeature(parent, e, nodeName);
				break;
			default:
				throwWarning("Unknown feature type: " + nodeName, e);
			}
		}
	}

	protected void parseFeature(IFeature parent, final Element e, final String nodeName) throws UnsupportedModelException {
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
					throwWarning("Unknown feature attribute: " + attributeName, e);
				}

			}
		}

		if (object.getFeature(name) != null) {
			throwError("Duplicate entry for feature: " + name, e);
		}

		if ((validator != null) && !validator.isValidFeatureName(name)) {
			addToProblemsList(name + " is not a valid feature name", e);
		}

		final IFeature f = factory.createFeature(object, name);
		f.getStructure().setMandatory(true);

		switch (nodeName) {
		case AND:
			f.getStructure().setAnd();
			break;
		case OR:
			f.getStructure().setOr();
			break;
		case ALT:
			f.getStructure().setAlternative();
			break;
		default:
			break;
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

	protected void parseProperty(IPropertyContainer properties, final Element e, String type) {
		if (!e.hasAttribute(KEY) || !e.hasAttribute(VALUE)) {
			throwWarning("Missing one of the required attributes: " + KEY + " or " + VALUE, e);
		} else {
			if (type == null) {
				type = e.hasAttribute(TYPE) ? e.getAttribute(TYPE) : TYPE_CUSTOM;
			}
			final String key = e.getAttribute(KEY);
			final String value = e.getAttribute(VALUE);
			if (properties.has(key, type)) {
				throwWarning("Redundant property definition for key: " + key, e);
			} else {
				properties.set(key, type, value);
			}
		}
	}

	protected void parseDescription(IFeature parent, final Element e) {
		if (e.getFirstChild() != null) {
			parent.getProperty().setDescription(getDescription(e.getFirstChild()));
		}
	}

	/**
	 * Parse the struct section to add features to the model.
	 */
	protected void parseStruct(List<Element> elements) throws UnsupportedModelException {
		for (final Element e : elements) {
			parseFeatures(e.getChildNodes(), null);
		}
	}

	protected void parseFeatureModelProperties(List<Element> elements) {
		for (final Element e : elements) {
			for (final Element propertyElement : getElements(e.getChildNodes())) {
				final String nodeName = propertyElement.getNodeName();
				switch (nodeName) {
				case GRAPHICS:
					parseProperty(object.getProperty(), propertyElement, GRAPHICS);
					break;
				case CALCULATIONS:
					parseProperty(object.getProperty(), propertyElement, CALCULATIONS);
					break;
				case PROPERTY:
					parseProperty(object.getProperty(), propertyElement, null);
					break;
				}
			}
		}
	}

	/**
	 * Parses the calculations section.
	 */
	protected void parseCalculations(List<Element> elements) throws UnsupportedModelException {
		for (final Element e : elements) {
			parseAttribute(e, CALCULATE_AUTO, CALCULATIONS);
			parseAttribute(e, CALCULATE_CONSTRAINTS, CALCULATIONS);
			parseAttribute(e, CALCULATE_FEATURES, CALCULATIONS);
			parseAttribute(e, CALCULATE_REDUNDANT, CALCULATIONS);
			parseAttribute(e, CALCULATE_TAUTOLOGY, CALCULATIONS);
		}
	}

	private void parseAttribute(final Element e, final String key, final String type) {
		if (e.hasAttribute(key)) {
			final String value = e.getAttribute(key);
			if (object.getProperty().has(key, type)) {
				throwWarning("Redundant property definition for key: " + key, e);
			} else {
				object.getProperty().set(key, type, value);
			}
		}
	}

	@Override
	protected void addProblem(final Problem problem) {
		localProblems.add(problem);
	}

	protected void writeAttributes(Element node, Element fnod, IFeature feat) {
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
		return new XmlFeatureModelFormat(this);
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return super.supportsContent(content, CONTENT_REGEX);
	}

	@Override
	public boolean supportsContent(LazyReader reader) {
		return super.supportsContent(reader, CONTENT_REGEX);
	}

	@Override
	public String getName() {
		return "FeatureIDE";
	}

	@Override
	public void setFeatureNameValidator(IFeatureNameValidator validator) {
		this.validator = validator;
	}

	@Override
	public IFeatureNameValidator getFeatureNameValidator() {
		return validator;
	}

}
