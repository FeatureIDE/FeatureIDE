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

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.AtMost;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Not;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.Text;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Entry;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Type;
import de.ovgu.featureide.fm.core.io.IFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Prints a feature model in XML format.
 *
 * @deprecated Use {@link XmlFeatureModelFormat} and {@link FileHandler} instead.
 *
 * @author Fabian Wielgorz
 * @author Dariusz Krolikowski
 * @author Maik Lampe
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public class XmlFeatureModelWriter extends AbstractXMLFeatureModelWriter<IFeatureModel> implements IFeatureModelWriter {

	public XmlFeatureModelWriter(IFeatureModel featureModel) {
		super(featureModel);
	}

	@Override
	protected void createXmlDoc(Document doc) {
		final Element root = doc.createElement(FEATURE_MODEL);
		final Element struct = doc.createElement(STRUCT);
		final Element properties = doc.createElement(PROPERTIES);
		final Element constraints = doc.createElement(CONSTRAINTS);
		final Element calculations = doc.createElement(CALCULATIONS);
		final Element comments = doc.createElement(COMMENTS);
		final Element order = doc.createElement(FEATURE_ORDER);
		// root.setAttribute(CHOSEN_LAYOUT_ALGORITHM, "" + featureModel.getGraphicRepresenation().getLayout().getLayoutAlgorithm());
		//
		// if (featureModel.getGraphicRepresenation().getLayout().verticalLayout() &&
		// !featureModel.getGraphicRepresenation().getLayout().hasFeaturesAutoLayout()) {
		// root.setAttribute(HORIZONTAL_LAYOUT, TRUE);
		// }
		// if (!featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures()) {
		// root.setAttribute(SHOW_HIDDEN_FEATURES, FALSE);
		// }

		doc.appendChild(root);
		root.appendChild(properties);
		createXmlPropertiesPart(doc, properties, object);

		root.appendChild(struct);
		createXmlDocRec(doc, struct, object.getStructure().getRoot().getFeature());

		root.appendChild(constraints);
		for (int i = 0; i < object.getConstraints().size(); i++) {
			Element rule;
			rule = doc.createElement(RULE);
			// if (!featureModel.getGraphicRepresenation().getLayout().hasFeaturesAutoLayout()) {
			// rule.setAttribute(COORDINATES, "" + featureModel.getConstraints().get(i).getGraphicRepresenation().getLocation().x + "," + " "
			// + featureModel.getConstraints().get(i).getGraphicRepresenation().getLocation().y);
			// }

			constraints.appendChild(rule);
			createPropositionalConstraints(doc, rule, object.getConstraints().get(i).getNode());
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

		Element fnod;
		List<IFeature> children;

		children = FeatureUtils.convertToFeatureList(feat.getStructure().getChildren());
		if (children.isEmpty()) {
			fnod = doc.createElement(FEATURE);
			final String description = feat.getProperty().getDescription();
			if (description != null) {
				final Element descr = doc.createElement(DESCRIPTION);
				descr.setTextContent("\n" + description.replace("\r", "") + "\n");
				fnod.appendChild(descr);
			}
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
			final String description = feat.getProperty().getDescription();
			if (description != null) {
				final Element descr = doc.createElement(DESCRIPTION);
				descr.setTextContent("\n" + description.replace("\r", "") + "\n");
				fnod.appendChild(descr);
			}

			writeAttributes(node, fnod, feat);

			final Iterator<IFeature> i = children.iterator();
			while (i.hasNext()) {
				createXmlDocRec(doc, fnod, i.next());
			}
		}
	}

	private void writeAttributes(Element node, Element fnod, IFeature feat) {
		fnod.setAttribute(NAME, feat.getName());
		if (feat.getStructure().isHidden()) {
			fnod.setAttribute(HIDDEN, TRUE);
		}
		if (feat.getStructure().isMandatory()) {
			fnod.setAttribute(MANDATORY, TRUE);
		}
		if (feat.getStructure().isAbstract()) {
			fnod.setAttribute(ABSTRACT, TRUE);
		}

		// if (!featureModel.getGraphicRepresenation().getLayout().showHiddenFeatures()
		// || !featureModel.getGraphicRepresenation().getLayout().hasFeaturesAutoLayout()) {
		// fnod.setAttribute(COORDINATES, +feat.getGraphicRepresenation().getLocation().x + ", " + feat.getGraphicRepresenation().getLocation().y);
		// }
		node.appendChild(fnod);
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

		Element op;
		if (node instanceof Literal) {
			Literal literal = (Literal) node;
			if (literal.positive) {
				op = doc.createElement(VAR);
				xmlNode.appendChild(op);
				op.appendChild(doc.createTextNode(node.toString()));
			} else {
				op = doc.createElement(NOT);
				xmlNode.appendChild(op);
				literal = literal.clone();
				literal.positive = true;
				createPropositionalConstraints(doc, op, literal);
			}
			return;
		}

		if (node instanceof And) {
			op = doc.createElement(CONJ);
			xmlNode.appendChild(op);
		} else if (node instanceof Or) {
			op = doc.createElement(DISJ);
			xmlNode.appendChild(op);
		} else if (node instanceof Not) {
			op = doc.createElement(NOT);
			xmlNode.appendChild(op);
		} else if (node instanceof Equals) {
			op = doc.createElement(EQ);
			xmlNode.appendChild(op);
		} else if (node instanceof Implies) {
			op = doc.createElement(IMP);
			xmlNode.appendChild(op);
		} else if (node instanceof AtMost) {
			op = doc.createElement(ATMOST1);
			xmlNode.appendChild(op);
		} else {
			op = doc.createElement(UNKNOWN);
			xmlNode.appendChild(op);
		}

		final org.prop4j.Node[] children = node.getChildren();

		for (int i = 0; i < children.length; i++) {
			createPropositionalConstraints(doc, op, children[i]);
		}
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return getObject();
	}

	@Override
	public void setFeatureModel(IFeatureModel featureModel) {
		setObject(featureModel);
	}

}
