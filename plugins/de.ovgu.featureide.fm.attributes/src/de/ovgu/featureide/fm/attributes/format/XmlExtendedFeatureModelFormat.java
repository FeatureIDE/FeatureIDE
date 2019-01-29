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
package de.ovgu.featureide.fm.attributes.format;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.COMMENTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.WRONG_SYNTAX;

import java.util.List;
import java.util.regex.Pattern;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.fm.attributes.base.AbstractFeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttributeParsedData;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeFactory;
import de.ovgu.featureide.fm.attributes.base.impl.FeatureAttributeParsedData;
import de.ovgu.featureide.fm.core.base.IFeature;
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

	public XmlExtendedFeatureModelFormat() {
		super();
	}

	protected XmlExtendedFeatureModelFormat(XmlExtendedFeatureModelFormat oldFormat) {
		super(oldFormat);
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		object.reset();

		factory = FMFactoryManager.getInstance().getFactory(object);

		for (final Element e : getElements(doc.getElementsByTagName(EXTENDED_FEATURE_MODEL))) {
			parseStruct(e.getElementsByTagName(STRUCT));
			parseConstraints(e.getElementsByTagName(CONSTRAINTS));
			parseCalculations(e.getElementsByTagName(CALCULATIONS));
			parseComments(e.getElementsByTagName(COMMENTS));
			parseFeatureOrder(e.getElementsByTagName(FEATURE_ORDER));
			parseFeatureModelProperties(e.getElementsByTagName(PROPERTIES));
		}

		if (object.getStructure().getRoot() == null) {
			throw new UnsupportedModelException(WRONG_SYNTAX, 1);
		}

		warnings.addAll(localProblems);
	}

	protected void writeDocument(Document doc) {
		final Element root = doc.createElement(EXTENDED_FEATURE_MODEL);
		doc.appendChild(root);

		writeProperties(doc, root);
		writeFeatures(doc, root);
		writeConstraints(doc, root);
		writeCalculations(doc, root);
		writeComments(doc, root);
		writeFeatureOrder(doc, root);
	}

	protected void createFeatureAttributes(Document doc, Element fnode, IFeature feature) {
		if (!(feature instanceof ExtendedFeature)) {
			return;
		}
		if ((((ExtendedFeature) feature).getAttributes() != null) && !((ExtendedFeature) feature).getAttributes().isEmpty()) {
			// Write FeatureAttributes into the XML
			for (final IFeatureAttribute featureAttribute : ((ExtendedFeature) feature).getAttributes()) {
				final Element attributeNode = doc.createElement(XMLFeatureModelTags.ATTRIBUTE);
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
			case PROPERTY:
				parseProperty(parent, e);
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

	protected void parseAttribute(IFeature parent, final Element e) throws UnsupportedModelException {
		if (e.hasAttributes()) {
			final NamedNodeMap nodeMapFeatureAttribute = e.getAttributes();
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
					throwError("Unknown feature attribute: " + attributeName, e);
				}
			}
			// TODO ATTRIBUTE Error marker for missing name and/or type
			final IFeatureAttributeParsedData parsedAttribute = new FeatureAttributeParsedData(name, type, unit, value, recursive, configurable);
			final IFeatureAttribute featureAttribute = attributeFactory.createFeatureAttribute(parsedAttribute, parent);
			if (featureAttribute != null) {
				((ExtendedFeature) parent).addAttribute(featureAttribute);
			}
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
			FMFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(XmlExtendedFeatureModelFormat.ID, ExtendedFeatureModelFactory.ID);
			return true;
		}
		return false;
	}

}
