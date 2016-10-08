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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.elements;

import java.util.Iterator;
import java.util.List;

import org.eclipse.draw2d.geometry.Point;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.xml.AXMLFormat;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Reads / Writes a graphical feature model.
 * 
 * @author Sebastian Krieter
 */
public class GraphicalFeatureModelFormat extends AXMLFormat<IGraphicalFeatureModel> {
	
	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + GraphicalFeatureModelFormat.class.getSimpleName();

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) {
		for (Element e : getElements(doc.getElementsByTagName("layout"))) {
			setFeatureModelAttributes(e);
			parseStruct(e.getElementsByTagName(STRUCT));
			parseConstraints(e.getElementsByTagName(CONSTRAINTS));
		}
	}

	private void setFeatureModelAttributes(Element eElement) {
		String algorithm = eElement.getAttribute(CHOSEN_LAYOUT_ALGORITHM);
		if (!algorithm.equals("")) {
			object.getLayout().setLayout(Integer.parseInt(algorithm));
		}
		String layout = eElement.getAttribute(HORIZONTAL_LAYOUT);
		if (layout.equals(TRUE)) {
			object.getLayout().verticalLayout(false);
		} else if (layout.equals(FALSE)) {
			object.getLayout().verticalLayout(true);
		}
		String showHidden = eElement.getAttribute(SHOW_HIDDEN_FEATURES);
		if (showHidden.equals(TRUE)) {
			object.getLayout().showHiddenFeatures(true);
		} else if (showHidden.equals(FALSE)) {
			object.getLayout().showHiddenFeatures(false);
		}
		String showShort = eElement.getAttribute(SHOW_SHORT_NAMES);
		if (showShort.equals(TRUE)) {
			object.getLayout().setShowShortNames(true);
		} else if (showShort.equals(FALSE)) {
			object.getLayout().setShowShortNames(false);
		}
	}

	private void parseStruct(NodeList struct) {
		for (Element e : getElements(struct)) {
			parseFeatures(e.getChildNodes());
		}
	}

	private void parseFeatures(NodeList nodeList) {
		Iterator<IGraphicalFeature> iterator = object.getFeatures().iterator();
		for (Element e : getElements(nodeList)) {
//			String nodeName = e.getNodeName();
			if (!iterator.hasNext()) {
				break;
			}
			IGraphicalFeature feature = iterator.next();

			if (e.hasAttributes()) {
				NamedNodeMap nodeMap = e.getAttributes();
				int x = 0;
				int y = 0;
				for (int i = 0; i < nodeMap.getLength(); i++) {
					org.w3c.dom.Node node = nodeMap.item(i);
					String attributeName = node.getNodeName();
					String attributeValue = node.getNodeValue();
					if (attributeName.equals("X")) {
						try {
							x = Integer.parseInt(attributeValue);
						} catch (NumberFormatException error) {
							// throwError(error.getMessage() + IS_NO_VALID_INTEGER_VALUE, child);
						}
					} else if (attributeName.equals("Y")) {
						try {
							y = Integer.parseInt(attributeValue);
						} catch (NumberFormatException error) {
							// throwError(error.getMessage() + IS_NO_VALID_INTEGER_VALUE, child);
						}
					} else {
						// throwError("Unknown constraint attribute: " + attributeName, node);
					}
				}
				feature.setLocation(new Point(x, y));
			}
		}
	}

	private void parseConstraints(NodeList struct) {
		for (Element e : getElements(struct)) {
			parseConstraint(e.getChildNodes());
		}
	}

	private void parseConstraint(NodeList nodeList) {
		Iterator<IGraphicalConstraint> iterator = object.getConstraints().iterator();
		for (Element e : getElements(nodeList)) {
//			String nodeName = e.getNodeName();
			if (!iterator.hasNext()) {
				break;
			}
			IGraphicalConstraint constraint = iterator.next();
			if (e.hasAttributes()) {
				NamedNodeMap nodeMap = e.getAttributes();
				int x = 0;
				int y = 0;
				for (int i = 0; i < nodeMap.getLength(); i++) {
					org.w3c.dom.Node node = nodeMap.item(i);
					String attributeName = node.getNodeName();
					String attributeValue = node.getNodeValue();
					if (attributeName.equals("X")) {
						try {
							x = Integer.parseInt(attributeValue);
						} catch (NumberFormatException error) {
							// throwError(error.getMessage() + IS_NO_VALID_INTEGER_VALUE, child);
						}
					} else if (attributeName.equals("Y")) {
						try {
							y = Integer.parseInt(attributeValue);
						} catch (NumberFormatException error) {
							// throwError(error.getMessage() + IS_NO_VALID_INTEGER_VALUE, child);
						}
					} else {
						// throwError("Unknown constraint attribute: " + attributeName, node);
					}
				}
				constraint.setLocation(new Point(x, y));
			}
		}
	}

	@Override
	protected void writeDocument(Document doc) {
		Element root = doc.createElement("layout");
		Element struct = doc.createElement(STRUCT);
		Element constraints = doc.createElement(CONSTRAINTS);
		root.setAttribute(CHOSEN_LAYOUT_ALGORITHM, Integer.toString(object.getLayout().getLayoutAlgorithm()));

		if (object.getLayout().verticalLayout() && !object.getLayout().hasFeaturesAutoLayout()) {
			root.setAttribute(HORIZONTAL_LAYOUT, TRUE);
		}
		if (!object.getLayout().showHiddenFeatures()) {
			root.setAttribute(SHOW_HIDDEN_FEATURES, FALSE);
		}
		if (object.getLayout().showShortNames()) {
			root.setAttribute(SHOW_SHORT_NAMES, TRUE);
		}

		doc.appendChild(root);

		root.appendChild(struct);
		root.appendChild(constraints);

		if (!object.getLayout().showHiddenFeatures() || !object.getLayout().hasFeaturesAutoLayout()) {
			for (IGraphicalFeature feat : object.getFeatures()) {
				final Element fnod = doc.createElement(FEATURE);
				fnod.setAttribute(NAME, feat.getObject().getName());

				final Point location = feat.getLocation();
				fnod.setAttribute("X", Integer.toString(location.x));
				fnod.setAttribute("Y", Integer.toString(location.y));
				struct.appendChild(fnod);
			}
		}

		if (!object.getLayout().hasFeaturesAutoLayout()) {
			for (IGraphicalConstraint constr : object.getConstraints()) {
				final Element rule = doc.createElement(RULE);
				final Point location = constr.getLocation();
				rule.setAttribute("X", Integer.toString(location.x));
				rule.setAttribute("Y", Integer.toString(location.y));
				constraints.appendChild(rule);
			}
		}
	}

	@Override
	public GraphicalFeatureModelFormat getInstance() {
		return new GraphicalFeatureModelFormat();
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
	public String getId() {
		return ID;
	}

}
