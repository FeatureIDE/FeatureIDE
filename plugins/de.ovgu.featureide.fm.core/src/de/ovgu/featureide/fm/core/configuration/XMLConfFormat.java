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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.util.List;
import java.util.regex.Pattern;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.AXMLFormat;
import de.ovgu.featureide.fm.core.io.xml.PositionalXMLHandler;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Extended configuration format for FeatureIDE projects in XML structure.
 *
 * @author Sebastian Krieter
 */
public class XMLConfFormat extends AXMLFormat<Configuration> implements IConfigurationFormat {

	private static final String NODE_FEATURE = "feature";
	private static final String ATTRIBUTE_NAME = "name";
	private static final String ATTRIBUTE_MANUAL = "manual";
	private static final String ATTRIBUTE_AUTOMATIC = "automatic";
	public static final String ID = PluginID.PLUGIN_ID + ".format.config." + XMLConfFormat.class.getSimpleName();
	public static final String EXTENSION = StringTable.CONF;

	private static final Pattern CONTENT_REGEX = Pattern.compile("\\A\\s*(<[?]xml\\s.*[?]>\\s*)?<configuration[\\s>]");

	@Override
	public XMLConfFormat getInstance() {
		return new XMLConfFormat();
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		object.resetValues();

		final Element root = doc.getDocumentElement();
		if (root == null) {
			warnings.add(new Problem("No root element specified", 1, Problem.Severity.ERROR));
			return;
		}
		if (root.getNodeName().equals("configuration")) {
			for (final Element feature : getElements(root.getElementsByTagName(NODE_FEATURE))) {
				final SelectableFeature selectablefeature;
				if (feature.hasAttribute(ATTRIBUTE_NAME)) {
					final String featureName = feature.getAttribute(ATTRIBUTE_NAME);
					selectablefeature = object.getSelectablefeature(object.getFeatureModel().getRenamingsManager().getNewName(featureName));
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
				}
				if (feature.hasAttribute(ATTRIBUTE_AUTOMATIC)) {
					selectablefeature.setAutomatic(getSelection(feature.getAttribute(ATTRIBUTE_AUTOMATIC), feature, warnings));
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
			}
		} else {
			warnings.add(new Problem("Root element must be <configuration>", 1, Problem.Severity.ERROR));
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
		final Element root = doc.createElement("configuration");
		doc.appendChild(root);
		for (final SelectableFeature feature : object.getFeatures()) {
			if ((feature.getManual() == Selection.UNDEFINED) && (feature.getAutomatic() == Selection.UNDEFINED)) {
				continue;
			}
			final Element featureNode = doc.createElement(NODE_FEATURE);
			featureNode.setAttribute(ATTRIBUTE_NAME, feature.getName());
			if (feature.getManual() != Selection.UNDEFINED) {
				featureNode.setAttribute(ATTRIBUTE_MANUAL, getSelectionString(feature.getManual()));
			}
			if (feature.getAutomatic() != Selection.UNDEFINED) {
				featureNode.setAttribute(ATTRIBUTE_AUTOMATIC, getSelectionString(feature.getAutomatic()));
			}
			root.appendChild(featureNode);

		}
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
		return "XML";
	}

}
