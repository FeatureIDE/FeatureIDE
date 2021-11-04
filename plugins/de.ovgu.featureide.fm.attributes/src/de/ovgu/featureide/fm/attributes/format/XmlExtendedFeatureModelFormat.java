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
package de.ovgu.featureide.fm.attributes.format;

import static de.ovgu.featureide.fm.core.localization.StringTable.COMMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.WRONG_SYNTAX;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttributeParsedData;
import de.ovgu.featureide.fm.attributes.base.exceptions.FeatureAttributeParseException;
import de.ovgu.featureide.fm.attributes.base.exceptions.UnknownFeatureAttributeTypeException;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeParsedData;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XMLFeatureModelTags;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;

/**
 * Implements the {@link IFeatureModelFormat} and represents the format used to read and write {@link ExtendedFeatureModel} to XML files.
 * 
 * @see IFeatureModelFormat
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class XmlExtendedFeatureModelFormat extends XmlFeatureModelFormat implements IFeatureModelFormat {

	public static final String ID = "de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat";

	private static final Pattern CONTENT_REGEX = Pattern.compile("\\A\\s*(<[?]xml\\s.*[?]>\\s*)?<" + EXTENDED_FEATURE_MODEL + "[\\s>]");

	protected final AbstractFeatureAttributeFactory attributeFactory = new FeatureAttributeFactory();

	private Map<String, Map<String, String>> recursiveLookup = new HashMap<>();

	public XmlExtendedFeatureModelFormat() {
		super();
	}

	protected XmlExtendedFeatureModelFormat(XmlExtendedFeatureModelFormat oldFormat) {
		super(oldFormat);
		factory = oldFormat.factory;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		object.reset();

		factory = FMFactoryManager.getInstance().getFactory(object);

		for (final Element e : getElement(doc, EXTENDED_FEATURE_MODEL, false)) {
			parseStruct(getElement(e, STRUCT, false));
			parseConstraints(getElement(e, CONSTRAINTS, true));
			parseComments(getElement(e, COMMENTS, true));
			parseFeatureOrder(getElement(e, FEATURE_ORDER, true));
			parseFeatureModelProperties(getElement(e, PROPERTIES, true));
		}

		handleRecursiveAttributes();

		if (object.getStructure().getRoot() == null) {
			throw new UnsupportedModelException(WRONG_SYNTAX, 1);
		}
		// handle recursive attributes
		List<IFeatureAttribute> recursiveAttributes = getRecursiveAttributes();
		for (IFeatureAttribute att : recursiveAttributes) {
			recurseAttributesWithLookup(att.getFeature(), att);
		}

		warnings.addAll(localProblems);
	}

	protected void createFeatureAttributes(Document doc, Element fnode, IFeature feature) {
		if (feature instanceof IExtendedFeature) {
			List<IFeatureAttribute> attributesList = ((IExtendedFeature) feature).getAttributes();
			if ((attributesList != null) && !attributesList.isEmpty()) {
				// Write FeatureAttributes into the XML
				for (final IFeatureAttribute featureAttribute : attributesList) {
					final Element attributeNode;
					if (featureAttribute.isRecursive() && !featureAttribute.isHeadOfRecursiveAttribute()) {
						createRecursedAttribute(doc, fnode, featureAttribute);
					} else {
						attributeNode = doc.createElement(XMLFeatureModelTags.ATTRIBUTE);
						attributeNode.setAttribute(XMLFeatureModelTags.NAME, featureAttribute.getName());
						attributeNode.setAttribute(XMLFeatureModelTags.ATTRIBUTE_TYPE, featureAttribute.getType());
						if (featureAttribute.getValue() != null) {
							attributeNode.setAttribute(XMLFeatureModelTags.ATTRIBUTE_VALUE, featureAttribute.getValue().toString());
						}
						attributeNode.setAttribute(XMLFeatureModelTags.ATTRIBUTE_UNIT, featureAttribute.getUnit());
						if (featureAttribute.isRecursive()) {
							attributeNode.setAttribute(XMLFeatureModelTags.ATTRIBUTE_RECURSIVE, XMLFeatureModelTags.TRUE);
						}
						if (featureAttribute.isConfigurable()) {
							attributeNode.setAttribute(XMLFeatureModelTags.ATTRIBUTE_CONFIGURABLE, XMLFeatureModelTags.TRUE);
						}
						fnode.appendChild(attributeNode);
					}
				}
			}
		}
	}

	/**
	 * Adds a feature attribute that is recursive but not the holder of the original recursive attribute to the xml-document
	 * 
	 * @param doc XML-document that is supposed to be edited
	 * @param fnode parent node
	 * @param att recursed feature attribute that is supposed to be added
	 */
	private void createRecursedAttribute(Document doc, Element fnode, IFeatureAttribute att) {
		final Element attributeNode = doc.createElement(XMLFeatureModelTags.ATTRIBUTE);
		if (att.getValue() == null) {
			return;
		}
		attributeNode.setAttribute(XMLFeatureModelTags.NAME, att.getName());
		attributeNode.setAttribute(XMLFeatureModelTags.ATTRIBUTE_VALUE, att.getValue().toString());
		fnode.appendChild(attributeNode);
	}

	@Override
	protected void writeDocument(Document doc) {
		final Element root = doc.createElement(EXTENDED_FEATURE_MODEL);
		doc.appendChild(root);

		writeProperties(doc, root);
		writeFeatures(doc, root);
		writeConstraints(doc, root);
		writeComments(doc, root);
		writeFeatureOrder(doc, root);
	}

	@Override
	protected void writeFeatureProperties(Document doc, Element node, IFeature feat, final Element fnod) {
		addDescription(doc, feat.getProperty().getDescription(), fnod);
		addProperties(doc, feat.getCustomProperties(), fnod);
		writeAttributes(node, fnod, feat);
		createFeatureAttributes(doc, fnod, feat);
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
			case ATTRIBUTE:
				parseAttribute(parent, e);
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

	protected void parseAttribute(IFeature parent, final Element element) throws UnsupportedModelException {
		if (element.hasAttributes()) {
			final NamedNodeMap nodeMapFeatureAttribute = element.getAttributes();
			String configurable = null;
			String recursive = null;
			String name = null;
			String unit = null;
			String value = null;
			String type = null;
			for (int i = 0; i < nodeMapFeatureAttribute.getLength(); i++) {
				final org.w3c.dom.Node node = nodeMapFeatureAttribute.item(i);
				final String attributeName = node.getNodeName();
				final String attributeValue = node.getNodeValue();

				if (attributeName.equals(ATTRIBUTE_CONFIGURABLE)) {
					configurable = attributeValue;
				} else if (attributeName.equals(ATTRIBUTE_RECURSIVE)) {
					recursive = attributeValue;
				} else if (attributeName.equals(NAME)) {
					name = attributeValue;
				} else if (attributeName.equals(ATTRIBUTE_UNIT)) {
					unit = attributeValue;
				} else if (attributeName.equals(ATTRIBUTE_VALUE)) {
					value = attributeValue;
				} else if (attributeName.equals(ATTRIBUTE_TYPE)) {
					type = attributeValue;
				} else {
					throwError("Unknown feature attribute: " + attributeName, element);
				}
			}
			// TODO ATTRIBUTE Error marker for missing name and/or type
			final IFeatureAttributeParsedData parsedAttribute = new FeatureAttributeParsedData(name, type, unit, value, recursive, configurable);
			if (parsedAttribute.isRecursed()) {
				addLookUpEntry(parent.getName(), name, value);
			} else {
				IFeatureAttribute featureAttribute;
				try {
					featureAttribute = attributeFactory.createFeatureAttribute(parsedAttribute, parent);
					if (featureAttribute != null) {
						((ExtendedFeature) parent).addAttribute(featureAttribute);
					}
				} catch (FeatureAttributeParseException | UnknownFeatureAttributeTypeException e) {
					Logger.logError(e);
				}
			}
		}
	}

	private void addLookUpEntry(String featureName, String attributeName, String value) {
		if (!recursiveLookup.containsKey(attributeName)) {
			recursiveLookup.put(attributeName, new HashMap<String, String>());
		}
		if (!recursiveLookup.get(attributeName).containsKey(featureName)) {
			recursiveLookup.get(attributeName).put(featureName, value);
		}
	}

	private void handleRecursiveAttributes() {
		// TODO Auto-generated method stub
	}

	private List<IFeatureAttribute> getRecursiveAttributes() {
		List<IFeatureAttribute> recursiveAttributes = new ArrayList<>();
		for (IFeature feat : object.getFeatures()) {
			ExtendedFeature ext = (ExtendedFeature) feat;
			for (IFeatureAttribute att : ext.getAttributes()) {
				if (att.isRecursive()) {
					recursiveAttributes.add(att);
				}
			}
		}
		return recursiveAttributes;
	}

	private void recurseAttributesWithLookup(IFeature feature, IFeatureAttribute attribute) {
		IFeatureAttribute newAttribute = null;
		for (IFeatureStructure struct : feature.getStructure().getChildren()) {
			ExtendedFeature feat = (ExtendedFeature) struct.getFeature();
			recurseAttributesWithLookup(feat, attribute);
			newAttribute = attribute.cloneRecursive(feat);
			String value = getValueFromLookup(feat.getName(), newAttribute.getName());
			addValueAccordingToType(newAttribute, value);
			if (!feat.isContainingAttribute(newAttribute)) {
				feat.addAttribute(newAttribute);
			}
		}
	}

	private String getValueFromLookup(String featName, String attributeName) {
		if (recursiveLookup.containsKey(attributeName)) {
			if (recursiveLookup.get(attributeName).containsKey(featName)) {
				return recursiveLookup.get(attributeName).get(featName);
			}
		}
		return null;
	}

	private void addValueAccordingToType(IFeatureAttribute attribute, String value) {
		if (value == null) {
			return;
		}
		switch (attribute.getType()) {
		case FeatureAttribute.BOOLEAN:
			Boolean valueBoolean = null;
			if (value != null) {
				valueBoolean = Boolean.parseBoolean(value);
			}
			attribute.setValue(valueBoolean);
			break;
		case FeatureAttribute.LONG:
			Long valueLong = null;
			if (value != null) {
				valueLong = Long.parseLong(value);
			}
			attribute.setValue(valueLong);
			break;
		case FeatureAttribute.DOUBLE:
			Double valueDouble = null;
			if (value != null) {
				valueDouble = Double.parseDouble(value);
			}
			attribute.setValue(valueDouble);
			break;
		case FeatureAttribute.STRING:
			String valueString = null;
			if (value != null) {
				valueString = value;
			}
			attribute.setValue(valueString);
			break;

		default:
			break;
		}
	}

	@Override
	public XmlExtendedFeatureModelFormat getInstance() {
		return new XmlExtendedFeatureModelFormat(this);
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
		return "FeatureIDE (Extended Feature Model)";
	}

	@Override
	public boolean initExtension() {
		if (super.initExtension()) {
			FMFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(ID, ExtendedFeatureModelFactory.ID);
			return true;
		}
		return false;
	}

}
