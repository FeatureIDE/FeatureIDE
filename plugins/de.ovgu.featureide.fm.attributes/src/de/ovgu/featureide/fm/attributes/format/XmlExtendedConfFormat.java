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

import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.fm.attributes.base.impl.ExtendedConfigurationFactory;
import de.ovgu.featureide.fm.attributes.config.ExtendedSelectableFeature;
import de.ovgu.featureide.fm.core.base.impl.ConfigurationFactoryManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.AXMLFormat;
import de.ovgu.featureide.fm.core.io.xml.PositionalXMLHandler;

public class XmlExtendedConfFormat extends AXMLFormat<Configuration> implements IConfigurationFormat {

	public static final String ID = "de.ovgu.featureide.fm.attributes.format.config.XmlExtendedConfFormat";
	private static final String NODE_FEATURE = "feature";
	private static final String NODE_ATTRIBUTE = "attribute";
	private static final String ATTRIBUTE_NAME = "name";
	private static final String ATTRIBUTE_VALUE = "value";
	private static final String ATTRIBUTE_MANUAL = "manual";
	private static final String ATTRIBUTE_AUTOMATIC = "automatic";
	public static final String EXTENSION = "econfig";
	private static final String EXTENDED_CONFIGURATION = "extendedConfiguration";
	private static final Pattern CONTENT_REGEX = Pattern.compile("\\A\\s*(<[?]xml\\s.*[?]>\\s*)?<" + EXTENDED_CONFIGURATION + "[\\s>]");

	@Override
	public String getName() {
		return "ExtendedXML";
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public XmlExtendedConfFormat getInstance() {
		return this;
	}

	public String getSuffix() {
		return "xml";
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		object.reset();
		final Element root = doc.getDocumentElement();
		if (root == null) {
			warnings.add(new Problem("No root element specified", 1, Problem.Severity.ERROR));
			return;
		}
		if (root.getNodeName().equals(EXTENDED_CONFIGURATION)) {
			for (final Element feature : getElements(root.getElementsByTagName(NODE_FEATURE))) {
				final SelectableFeature selectablefeature;
				if (feature.hasAttribute(ATTRIBUTE_NAME)) {
					final String featureName = feature.getAttribute(ATTRIBUTE_NAME);
					selectablefeature = object.getSelectableFeature(featureName, true);
					if (selectablefeature == null) {
						createWarning("Invalid feature name: " + featureName, feature, warnings);
						continue;
					}
				} else {
					createError("No feature name specified", feature, warnings);
					continue;
				}

				if (feature.hasAttribute(ATTRIBUTE_MANUAL)) {
					selectablefeature.setManual(getSelection(feature.getAttribute(ATTRIBUTE_MANUAL), feature, warnings));
				} else {
					createWarning("No manual selection state specified", feature, warnings);
					continue;
				}

				if (feature.hasAttribute(ATTRIBUTE_AUTOMATIC)) {
					selectablefeature.setAutomatic(getSelection(feature.getAttribute(ATTRIBUTE_AUTOMATIC), feature, warnings));
				} else {
					createWarning("No automatic selection state specified", feature, warnings);
					continue;
				}

				final NamedNodeMap attributes = feature.getAttributes();
				if (attributes.getLength() > 3) {
					for (int i = 0; i < attributes.getLength(); i++) {
						final String attributeName = attributes.item(i).getNodeName();
						switch (attributeName) {
						case ATTRIBUTE_NAME:
						case ATTRIBUTE_MANUAL:
						case ATTRIBUTE_AUTOMATIC:
							break;
						default:
							createWarning("Unknown attribute: " + attributeName, feature, warnings);
							break;
						}
					}
				}
				if (selectablefeature instanceof ExtendedSelectableFeature) {
					final NodeList attributeNodes = feature.getChildNodes();
					for (int i = 0; i < attributeNodes.getLength(); i++) {
						Node currentItem = attributeNodes.item(i);
						if (currentItem.hasAttributes() && currentItem.getAttributes().getNamedItem(ATTRIBUTE_NAME) != null) {
							((ExtendedSelectableFeature) selectablefeature).addConfigurableAttribute(
									currentItem.getAttributes().getNamedItem(ATTRIBUTE_NAME).getNodeValue(),
									currentItem.getAttributes().getNamedItem(ATTRIBUTE_VALUE).getNodeValue());
						}
					}
				}
			}

		} else {
			warnings.add(new Problem("Root element must be <extendedConfiguration>", 1, Problem.Severity.ERROR));
		}
	}

	protected void createWarning(final String message, Element element, List<Problem> warnings) {
		final Object lineNumber = element.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME);
		warnings.add(new Problem(message, (lineNumber instanceof Integer) ? (int) lineNumber : 1, Problem.Severity.WARNING));
	}

	protected void createError(final String message, Element element, List<Problem> warnings) {
		final Object lineNumber = element.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME);
		warnings.add(new Problem(message, (lineNumber instanceof Integer) ? (int) lineNumber : 1, Problem.Severity.ERROR));
	}

	private Selection getSelection(String selection, Element feature, List<Problem> warnings) {
		if (selection == null) {
			createError("Selection state not specified" + selection, feature, warnings);
			return Selection.UNDEFINED;
		} else {
			switch (selection) {
			case "selected":
				return Selection.SELECTED;
			case "undefined":
				return Selection.UNDEFINED;
			case "unselected":
				return Selection.UNSELECTED;
			default:
				createError("Invalid selection state: " + selection, feature, warnings);
				return Selection.UNDEFINED;
			}
		}
	}

	private String getSelectionString(Selection selection) {
		switch (selection) {
		case SELECTED:
			return "selected";
		case UNDEFINED:
			return "undefined";
		case UNSELECTED:
			return "unselected";
		default:
			throw new RuntimeException(selection.toString());
		}
	}

	@Override
	protected void writeDocument(Document doc) {
		final Element root = doc.createElement(EXTENDED_CONFIGURATION);
		doc.appendChild(root);
		for (final SelectableFeature feature : object.getFeatures()) {
			final Element featureNode = doc.createElement(NODE_FEATURE);
			featureNode.setAttribute(ATTRIBUTE_NAME, feature.getName());
			featureNode.setAttribute(ATTRIBUTE_MANUAL, getSelectionString(feature.getManual()));
			featureNode.setAttribute(ATTRIBUTE_AUTOMATIC, getSelectionString(feature.getAutomatic()));
			root.appendChild(featureNode);
			if (feature instanceof ExtendedSelectableFeature) {
				for (Map.Entry<String, String> entry : ((ExtendedSelectableFeature) feature).getConfigurableAttributes().entrySet()) {
					final Element attributeNode = doc.createElement(NODE_ATTRIBUTE);
					attributeNode.setAttribute(ATTRIBUTE_NAME, entry.getKey());
					attributeNode.setAttribute(ATTRIBUTE_VALUE, entry.getValue().toString());
					featureNode.appendChild(attributeNode);
				}
			}
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

	@Override
	public boolean supportsContent(CharSequence content) {
		return super.supportsContent(content, CONTENT_REGEX);
	}

	@Override
	public boolean supportsContent(LazyReader content) {
		return super.supportsContent(content, CONTENT_REGEX);
	}

	@Override
	public boolean initExtension() {
		if (super.initExtension()) {
			ConfigurationFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(ID, ExtendedConfigurationFactory.ID);
			return true;
		}
		return false;
	}

}
