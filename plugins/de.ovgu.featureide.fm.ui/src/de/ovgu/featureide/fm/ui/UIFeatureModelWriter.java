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
package de.ovgu.featureide.fm.ui;

import java.util.List;

import org.eclipse.draw2d.geometry.Point;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.AXMLFormat;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * 
 * @author Sebastian Krieter
 */
public class UIFeatureModelWriter extends AXMLFormat<IGraphicalFeatureModel> {

	@Override
	public IPersistentFormat<IGraphicalFeatureModel> getInstance() {
		return this;
	}

	@Override
	public boolean supportsRead() {
		return false;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return null;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
	}

	@Override
	protected void writeDocument(Document doc) {
		Element root = doc.createElement(FEATURE_MODEL);
		root.setAttribute(CHOSEN_LAYOUT_ALGORITHM, "" + object.getLayout().getLayoutAlgorithm());

		if (object.getLayout().verticalLayout() && !object.getLayout().hasFeaturesAutoLayout()) {
			root.setAttribute(HORIZONTAL_LAYOUT, TRUE);
		}
		if (!object.getLayout().showHiddenFeatures()) {
			root.setAttribute(SHOW_HIDDEN_FEATURES, FALSE);
		}

		doc.appendChild(root);

		if (!object.getLayout().hasFeaturesAutoLayout()) {
			Element featuresNode = doc.createElement(FEATURES);
			root.appendChild(featuresNode);
			for (IGraphicalFeature feature : object.getFeatures()) {
				Element element = doc.createElement(FEATURE);
				final String featureName = feature.getObject().getName();
				if (featureName != null) {
					element.setAttribute(NAME, featureName);
				} else {
					FMCorePlugin.getDefault().logWarning("No Feature Name!");
				}
				final Point location = feature.getLocation();
				element.setAttribute(COORDINATES, location.x + ", " + location.y);
				featuresNode.appendChild(element);
			}

			Element constraintsNode = doc.createElement(CONSTRAINTS);
			root.appendChild(constraintsNode);
			for (IGraphicalConstraint constraint : object.getConstraints()) {
				Element rule;
				rule = doc.createElement(CONSTRAINT);
				final String constraintName = constraint.getObject().getName();
				if (constraintName != null) {
					rule.setAttribute(NAME, constraintName);
				}
				final Point location = constraint.getLocation();
				rule.setAttribute(COORDINATES, location.x + ", " + location.y);
				constraintsNode.appendChild(rule);
			}
		}		
	}

}
