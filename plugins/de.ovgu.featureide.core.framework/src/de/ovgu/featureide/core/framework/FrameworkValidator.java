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

		if (!file.exists())
			return false;
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
	 * class for validating XML file depending on dtd file
	 * <p>
	 * {@code TODO missing implementation}
	 * 
	 * @author Daniel Hohmann
	 */
	@SuppressWarnings("unused")
	private class XMLValidator {

		boolean validateWithDTD(IFile file) throws ParserConfigurationException, SAXException, MalformedURLException, IOException {
			SAXParserFactory factory = SAXParserFactory.newInstance();
			factory.setValidating(true);
			factory.setNamespaceAware(true);

			SAXParser parser = factory.newSAXParser();

			XMLReader reader = parser.getXMLReader();
			
			reader.setErrorHandler(new ErrorHandler(){

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
