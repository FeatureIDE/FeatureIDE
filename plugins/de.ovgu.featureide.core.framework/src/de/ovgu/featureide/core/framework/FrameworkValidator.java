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
package de.ovgu.featureide.core.framework;

import java.io.IOException;
import java.net.MalformedURLException;

import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import org.eclipse.core.resources.IFile;
import org.xml.sax.ErrorHandler;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;
import org.xml.sax.XMLReader;

public class FrameworkValidator {

	/**
	 * Checks given file
	 *
	 * @param file
	 * @return <code>true</code> if file is correct
	 */
	public static boolean validate(IFile file) {

		if (!file.exists()) {
			return false;
		}
		return true;
	}

	/**
	 * Validates content of info.xml file
	 *
	 * @param info - info.xml file
	 * @return <code>true</code>, if it is correct
	 */
	public static boolean validateContent(IFile info) {
		return false;
	}

	/**
	 *
	 * class for validating XML file depending on dtd file <p> {@code TODO missing implementation}
	 *
	 * @author Daniel Hohmann
	 */
	@SuppressWarnings("unused")
	private class XMLValidator {

		boolean validateWithDTD(IFile file) throws ParserConfigurationException, SAXException, MalformedURLException, IOException {
			final SAXParserFactory factory = SAXParserFactory.newInstance();
			factory.setValidating(true);
			factory.setNamespaceAware(true);

			final SAXParser parser = factory.newSAXParser();

			final XMLReader reader = parser.getXMLReader();

			reader.setErrorHandler(new ErrorHandler() {

				@Override
				public void error(SAXParseException arg0) throws SAXException {
					// TODO Auto-generated method stub

				}

				@Override
				public void fatalError(SAXParseException arg0) throws SAXException {
					// TODO Auto-generated method stub

				}

				@Override
				public void warning(SAXParseException arg0) throws SAXException {
					// TODO Auto-generated method stub

				}

			});
			reader.parse(new InputSource(file.getLocationURI().toURL().openStream()));
			return false;
		}
	}
}
