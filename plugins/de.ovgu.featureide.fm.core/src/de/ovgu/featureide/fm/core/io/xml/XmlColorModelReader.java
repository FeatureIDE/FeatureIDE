/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.xml;

import java.io.InputStream;
import java.util.Iterator;

import javax.xml.stream.XMLEventReader;
import javax.xml.stream.XMLInputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.Attribute;
import javax.xml.stream.events.EndElement;
import javax.xml.stream.events.StartElement;
import javax.xml.stream.events.XMLEvent;

import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Parses the color model from XML to the feature model
 * 
 * @author Sebastian Krieter
 */
public class XmlColorModelReader extends XmlFeatureModelReader {

	public XmlColorModelReader(FeatureModel featureModel) {
		super(featureModel);
	}

	@Override
	protected synchronized void parseInputStream(InputStream inputStream)
			throws UnsupportedModelException {
		try {
			XMLEventReader eventReader = XMLInputFactory.newInstance().createXMLEventReader(inputStream);

			// mode: 0 = start; 1 = feature; 2 = colorSchemes; 3 = features;
			int mode = 0;

			ColorschemeTable colorschemeTable = featureModel.getColorschemeTable();
			ColorList colors = null;
			
			colorschemeTable.clearBeforeLoading();

			while (eventReader.hasNext()) {
				XMLEvent event = eventReader.nextEvent();
				if (event.isStartElement()) {
					StartElement currentStartTag = event.asStartElement();
					String currentTag = currentStartTag.getName()
							.getLocalPart();

					if (mode == 1 && currentTag.equals("color")) {
						
						@SuppressWarnings("unchecked")
						Iterator<Attribute> attributes = currentStartTag.getAttributes();
						Attribute indexAttribute = attributes.next();
						Attribute schemeAttribute = attributes.next();
						
						if (schemeAttribute.getName().getLocalPart().equals("scheme") &&
								indexAttribute.getName().getLocalPart().equals("index")) {
							colors.setColor(Integer.parseInt(schemeAttribute.getValue()), 
									Integer.parseInt(indexAttribute.getValue()));
						}
					} else if (mode == 2) {
						@SuppressWarnings("unchecked")
						Iterator<Attribute> attributes = currentStartTag.getAttributes();
						
						if (attributes.hasNext()) {
							Attribute attribute = attributes.next();
							String curName = attribute.getName().getLocalPart();
							String curValue = attribute.getValue();
							
							if (currentTag.equals("colorscheme") && curName.equals("name")) {
								colorschemeTable.addColorscheme(curValue);
							} else if (currentTag.equals("curColorscheme") && curName.equals("index")) {
								colorschemeTable.setSelectedColorscheme(Integer.parseInt(curValue));
							}
						}
					} else if (mode == 3 && currentTag.equals("feature")) {
						Attribute attribute = (Attribute) currentStartTag.getAttributes().next();
						if (attribute.getName().getLocalPart().equals("name")) {
							Feature feat = featureModel.getFeature(featureModel.getRenamingsManager().getNewName(attribute.getValue()));
							if (feat != null) {
								colors = feat.getColorList();
								mode = 1;
							}
						}
					} else {
						if (currentTag.equals("colorSchemes")) {
							mode = 2;
						} else if (currentTag.equals("features")) {
							mode = 3;
						}
					}
				} else if (event.isEndElement()) {
					EndElement endElement = event.asEndElement();
					String currentTag = endElement.getName().getLocalPart();

					if (mode == 1 && currentTag.equals("feature")) {
						mode = 3;
					} else if (mode == 2 && currentTag.equals("colorSchemes")) {
						mode = 0;
					} else if (mode == 3 && currentTag.equals("features")) {
						mode = 0;
					}
				}
			}
			colorschemeTable.checkAfterLoading();
			
			eventReader.close();
			
		} catch (XMLStreamException e) {
			throw new UnsupportedModelException(e.getMessage(), e.getLocation().getLineNumber());
		}
	}
}