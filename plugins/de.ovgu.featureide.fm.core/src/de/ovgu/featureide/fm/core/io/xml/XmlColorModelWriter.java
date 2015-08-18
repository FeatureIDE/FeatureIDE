/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.COLOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.COLORSCHEME;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.INDEX;
import static de.ovgu.featureide.fm.core.localization.StringTable.SCHEME;

import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Prints the colorschemes for the feature model in XML format.
 * 
 * @author Sebastian Krieter
 */
public class XmlColorModelWriter extends XmlFeatureModelWriter {
	
	public XmlColorModelWriter(IFeatureModel featureModel) {
		super(featureModel);
	}
	
	/**
	 * Creates XML-Document
	 * @param doc document to write
	 */
	@Override
	protected void createXmlDoc(Document doc) {
    	Element root = doc.createElement("root");
    	Element colorSchemesRoot = doc.createElement("colorSchemes");
    	Element featuresRoot = doc.createElement(FEATURES);

    	ColorschemeTable colorschemeTable = featureModel.getColorschemeTable();
    	List<String> csNames = colorschemeTable.getColorschemeNames();
    	for (String name : csNames) {
    		Element colorSchemesElement = doc.createElement(COLORSCHEME);
    		colorSchemesElement.setAttribute("name", name);
    		colorSchemesRoot.appendChild(colorSchemesElement);
		}
    	Element curSchemeElement = doc.createElement("curColorscheme");
    	curSchemeElement.setAttribute(INDEX, Integer.toString(colorschemeTable.getSelectedColorscheme()));
		colorSchemesRoot.appendChild(curSchemeElement);
    	
    	root.appendChild(colorSchemesRoot);
    	
		for (IFeature feat : featureModel.getFeatures()) {
			ColorList colors = feat.getColorList();

			boolean noColor = true;
			Element featuresElement = null;

			for (int i = 1; i <= colorschemeTable.size(); i++) {
				if (colors.hasColor(i)) {
					if (noColor) {
						featuresElement = doc.createElement("feature");
						featuresElement.setAttribute("name", feat.getName());
						noColor = false;
					}
					Element colorElement = doc.createElement(COLOR);
					colorElement.setAttribute( INDEX,	Integer.toString(colors.getColor(i)));
					colorElement.setAttribute(SCHEME, Integer.toString(i));
					featuresElement.appendChild(colorElement);
				}
			}

			if (featuresElement != null) {
				featuresRoot.appendChild(featuresElement);
			}
		}
    	
    	root.appendChild(featuresRoot);
    	doc.appendChild(root);
    }
}
