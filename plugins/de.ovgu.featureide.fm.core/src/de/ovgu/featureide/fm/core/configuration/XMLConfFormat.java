/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
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

	@Override
	public IPersistentFormat<Configuration> getInstance() {
		return this;
	}

	@Override
	public boolean supportsRead() {
		return false;
	}

	@Override
	public boolean supportsWrite() {
		return false;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		final Element root = doc.getDocumentElement();
		if (root == null) {
			warnings.add(new Problem("No root element specified", 1, Problem.Severity.ERROR));
			return;
		}
		if (root.getNodeName().equals("configuration")) {
			for (Element feature : getElements(root.getElementsByTagName(NODE_FEATURE))) {
				final SelectableFeature selectablefeature;
				if (feature.hasAttribute(ATTRIBUTE_NAME)) {
					final String featureName = feature.getAttribute(ATTRIBUTE_NAME);
					selectablefeature = object.getSelectablefeature(featureName);
					if (selectablefeature == null) {
						createWarning("Invalid feature name: " + featureName, feature, warnings);
						continue;
					}
				} else {
					createWarning("No feature name specified", feature, warnings);
					continue;
				}

				if (feature.hasAttribute(ATTRIBUTE_AUTOMATIC)) {
					selectablefeature.setAutomatic(getSelection(feature.getAttribute(ATTRIBUTE_AUTOMATIC), feature, warnings));
				} else {
					createWarning("No automatic selection state specified", feature, warnings);
					continue;
				}

				if (feature.hasAttribute(ATTRIBUTE_MANUAL)) {
					selectablefeature.setManual(getSelection(feature.getAttribute(ATTRIBUTE_MANUAL), feature, warnings));
				} else {
					createWarning("No manual selection state specified", feature, warnings);
					continue;
				}
			}
		} else {
			warnings.add(new Problem("Root element must be <configuration>", 1, Problem.Severity.ERROR));
		}
	}

	protected void createWarning(final String message, Element feature, List<Problem> warnings) {
		final Object lineNumber = feature.getUserData(PositionalXMLHandler.LINE_NUMBER_KEY_NAME);
		warnings.add(new Problem(message, (lineNumber instanceof Integer) ? (int) lineNumber : 1, Problem.Severity.WARNING));
	}

	private Selection getSelection(String selection, Element feature, List<Problem> warnings) {
		if (selection == null) {
			createWarning("Selection state not specified" + selection, feature, warnings);
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
				createWarning("Invalid selection state: " + selection, feature, warnings);
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
		Element root = doc.createElement("configuration");
		doc.appendChild(root);
		for (SelectableFeature feature : object.getFeatures()) {
			Element featureNode = doc.createElement(NODE_FEATURE);
			featureNode.setAttribute(ATTRIBUTE_NAME, feature.getName());
			featureNode.setAttribute(ATTRIBUTE_MANUAL, getSelectionString(feature.getManual()));
			featureNode.setAttribute(ATTRIBUTE_AUTOMATIC, getSelectionString(feature.getAutomatic()));
			root.appendChild(featureNode);
		}
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return supportsRead();
	}

}
