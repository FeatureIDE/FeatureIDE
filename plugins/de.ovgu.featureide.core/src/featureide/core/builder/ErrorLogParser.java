/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.core.builder;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import featureide.core.CorePlugin;

/**
 * Opens the specified xml-file. Used for creating ErrorMessage-Objects
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class ErrorLogParser {
	
	/**
	 * the xml-file
	 */
	private File xmlFile;
	
	/**
	 * the parsed xml-file
	 */
	private Document dom;


	public ErrorLogParser(String xmlFile) {
		this.xmlFile = new File(xmlFile);
		load();
	}

	private void load() {
		DocumentBuilder parser;
		try {
			parser = DocumentBuilderFactory.newInstance().newDocumentBuilder();
			try {
				if (xmlFile.exists()) {
					CorePlugin.getDefault().logInfo("piep");
					dom = parser.parse(xmlFile);
				}
				else CorePlugin.getDefault().logInfo("Could not find file");
			} catch (SAXException e) {
				CorePlugin.getDefault().logError(e);
			} catch (IOException e) {
				CorePlugin.getDefault().logError(e);
			}
		} catch (ParserConfigurationException e1) {
			CorePlugin.getDefault().logError(e1);
		}
	}

	public ArrayList<ErrorMessage> createErrorMessages() {
		ArrayList<ErrorMessage> errorMessages = new ArrayList<ErrorMessage>();
		NodeList elements = dom.getDocumentElement()
				.getElementsByTagName("MSG");
		if (elements != null) {
			for (int i = 0; i < elements.getLength(); i++) {
				ErrorMessage error = new ErrorMessage();
				error.setMessage(elements.item(i).getTextContent());
				CorePlugin.getDefault().logInfo(error.getMessage());
				NamedNodeMap attr = elements.item(i).getAttributes();
				if (attr != null) {
					for (int j = 0; j < attr.getLength(); j++) {
						if (attr.item(j).toString().contains("file"))
							error.setFile(attr.item(j).getNodeValue());
						if (attr.item(j).toString().contains("line"))
							error.setLine(Integer.parseInt(attr.item(j).getNodeValue()));
						if (attr.item(j).toString().contains("type"))
							error.setType(attr.item(j).getNodeValue());
					}
				}
				errorMessages.add(error);
				CorePlugin.getDefault().logInfo(error.toString());
			}
		}
		return errorMessages;
	}

}
