package de.ovgu.featureide.core.framework;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.resources.IFile;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import de.ovgu.featureide.core.framework.activator.FrameworkCorePlugin;

public class FrameworkValidator {
	/**
	 * Checks given file
	 * @param file
	 * @return <code>true</code> if file is correct
	 */
	public static boolean validate(IFile file){
		
		if(!file.exists()) return false;
		return true;
	}
	/**
	 * Validates content of info.xml file
	 * @param info - info.xml file
	 * @return <code>true</code>, if it is correct
	 */
	public static boolean validateContent(IFile info){
		URL url = null;
		try {
			url = new URL(info.getFullPath().toString());
		} catch (MalformedURLException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		
		if(url == null) return false;
		
		DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
		DocumentBuilder dBuilder = null;
		Document doc = null;
		try {
			dBuilder = dbFactory.newDocumentBuilder();
		} catch (ParserConfigurationException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		try {
			 doc = dBuilder.parse(url.openStream());
		} catch (SAXException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
		
		if(doc == null) return false;
		
		boolean isNeededFile = false;
		
		NodeList firstStage = doc.getChildNodes();
		for(int i=0; i<firstStage.getLength(); i++){
			Node node = firstStage.item(i);
			if(node.getNodeName().equals("plugin")){
				isNeededFile = true;
				NodeList secondStage = node.getChildNodes();
				if(secondStage.getLength() == 0) return false;
				for(int j=0; j<secondStage.getLength(); j++){
					if(!secondStage.item(j).getNodeName().equals("interface")) return false;
				}
			}
		}
		return isNeededFile;
	}
}
