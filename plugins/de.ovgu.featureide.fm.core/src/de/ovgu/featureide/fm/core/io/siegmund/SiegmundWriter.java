/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.core.io.siegmund;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerFactoryConfigurationError;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelWriter;

/**
 * Prints a feature model in XML format.
 * 
 * @author Dariusz Krolikowski
 * @author Maik Lampe
 * @author Thomas Thuem
 */
public class SiegmundWriter extends AbstractFeatureModelWriter {
		
	public SiegmundWriter() {
	}
	
	/**
	 * Creates a new writer and sets the feature model to write out.
	 * 
	 * @param featureModel the structure to write
	 */
	public SiegmundWriter(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
	/**
	 * Creates XML-Document
	 * @param doc document to write
	 */
    private void createXmlDoc(Document doc) {
        Element plm = doc.createElement("plm");
    	doc.appendChild(plm);
		plm.setAttribute("name", featureModel.getRoot().getName());
		plm.setAttribute("canReuseInstance", "true");
		
		Map<String,Set<String>> requires = new HashMap<String, Set<String>>();
		Map<String,Set<String>> excludes = new HashMap<String, Set<String>>();
    	List<Node> furtherNodes = new LinkedList<Node>();
    	Node node = new And(featureModel.getPropositionalNodes());
    	if (node.getChildren().length > 0) {
        	node = node.toCNF();
        	if (!(node instanceof And))
        		node = new And(node);
        	for (Node child : node.getChildren()) {
        		if (child instanceof Or && child.getChildren().length == 2) {
        			Literal literalA = (Literal) child.getChildren()[0];
        			Literal literalB = (Literal) child.getChildren()[1];
        			if (!literalA.positive || !literalB.positive) {
        				if (literalA.positive) {
        					Literal temp = literalA;
        					literalA = literalB;
        					literalB = temp;
        				}
        				if (literalB.positive) {
        					Set<String> set = requires.get(literalA.var);
        					if (set == null) {
        						set = new HashSet<String>();
        						requires.put(literalA.var.toString(), set);
        					}
        					set.add(literalB.var.toString());
        				}
        				else {
        					Set<String> set = excludes.get(literalA.var);
        					if (set == null) {
        						set = new HashSet<String>();
        						excludes.put(literalA.var.toString(), set);
        					}
        					set.add(literalB.var.toString());
        				}
        			}
            		else
            			furtherNodes.add(child);
        		}
        		else
        			furtherNodes.add(child);
        	}
    	}

    	for (Feature feature : featureModel.getFeatures())
        	createXmlDocRec(doc, plm, feature, requires.get(feature.getName()), excludes.get(feature.getName()));
    	
    	plm.appendChild(doc.createElement("properties"));

    	Element furtherConstraints = doc.createElement("furtherConstraints");
    	plm.appendChild(furtherConstraints);
    	for (Node child : furtherNodes) {
			Element clause = doc.createElement("clause");
			furtherConstraints.appendChild(clause);
			clause.appendChild(doc.createTextNode(child.toString()));
		}
    }
    
    /**
     * Creates document based on feature model step by step
     * @param doc document to write
     * @param node parent node
     * @param feature current feature
     * @param exclude 
     * @param require 
     */
    private void createXmlDocRec(Document doc, Element node, Feature feature, Set<String> require, Set<String> exclude) {
    	Element element = doc.createElement("element");
    	node.appendChild(element);
		element.setAttribute("id", feature.getName());
		element.setAttribute("name", feature.getName());
		element.setAttribute("type", "feature");
		element.setAttribute("optional", feature.isMandatory() ? "false" : "true");
		element.setAttribute("dynamic", "false");
    	
    	element.appendChild(doc.createElement("path_absolut"));
    	element.appendChild(doc.createElement("path_relativ"));

    	if (!feature.isRoot()) {
        	Element parentElement = doc.createElement("parentElement");
        	element.appendChild(parentElement);
        	Element id = doc.createElement("id");
        	parentElement.appendChild(id);
        	id.appendChild(doc.createTextNode(feature.getParent().getName()));
    	}
    	
    	Element constraints = doc.createElement("constraints");
    	element.appendChild(constraints);
    	
    	Element alternative = doc.createElement("constraint");
    	constraints.appendChild(alternative);
		alternative.setAttribute("type", "alternative");
    	if (!feature.isRoot() && feature.getParent().isAlternative()) {
        	for (Feature childFeature : feature.getParent().getChildren())
        		if (childFeature != feature) {
	            	Element constraint_element = doc.createElement("constraint_element");
	            	alternative.appendChild(constraint_element);
	            	Element id = doc.createElement("id");
	            	constraint_element.appendChild(id);
	            	id.appendChild(doc.createTextNode(childFeature.getName()));
	            	Element name = doc.createElement("name");
	            	constraint_element.appendChild(name);
	            	name.appendChild(doc.createTextNode(childFeature.getName()));
	    		}
    	}

    	Element commulative = doc.createElement("constraint");
    	constraints.appendChild(commulative);
    	commulative.setAttribute("type", "commulative");
    	if (!feature.isRoot() && feature.getParent().isOr()) {
        	for (Feature childFeature : feature.getParent().getChildren())
        		if (childFeature != feature) {
	            	Element constraint_element = doc.createElement("constraint_element");
	            	commulative.appendChild(constraint_element);
	            	Element id = doc.createElement("id");
	            	constraint_element.appendChild(id);
	            	id.appendChild(doc.createTextNode(childFeature.getName()));
	            	Element name = doc.createElement("name");
	            	constraint_element.appendChild(name);
	            	name.appendChild(doc.createTextNode(childFeature.getName()));
	    		}
    	}

    	Element requires = doc.createElement("constraint");
    	constraints.appendChild(requires);
    	requires.setAttribute("type", "requires");
    	if (require != null)
	    	for (String childFeature : require) {
	        	Element constraint_element = doc.createElement("constraint_element");
	        	requires.appendChild(constraint_element);
	        	Element id = doc.createElement("id");
	        	constraint_element.appendChild(id);
	        	id.appendChild(doc.createTextNode(childFeature));
	        	Element name = doc.createElement("name");
	        	constraint_element.appendChild(name);
	        	name.appendChild(doc.createTextNode(childFeature));
			}

    	Element excludes = doc.createElement("constraint");
    	constraints.appendChild(excludes);
    	excludes.setAttribute("type", "excludes");
    	if (exclude != null)
	    	for (String childFeature : exclude) {
	        	Element constraint_element = doc.createElement("constraint_element");
	        	excludes.appendChild(constraint_element);
	        	Element id = doc.createElement("id");
	        	constraint_element.appendChild(id);
	        	id.appendChild(doc.createTextNode(childFeature));
	        	Element name = doc.createElement("name");
	        	constraint_element.appendChild(name);
	        	name.appendChild(doc.createTextNode(childFeature));
			}
    	
    	Element childElements = doc.createElement("childElements");
    	element.appendChild(childElements);
    	for (Feature childFeature : feature.getChildren()) {
        	Element child = doc.createElement("child");
        	childElements.appendChild(child);
    		child.setAttribute("optional", childFeature.isMandatory() ? "false" : "true");
        	Element id = doc.createElement("id");
        	child.appendChild(id);
        	id.appendChild(doc.createTextNode(childFeature.getName()));
		}
    	
    	element.appendChild(doc.createElement("order"));
    	element.appendChild(doc.createElement("classes"));
    }
  
    /**
     * Inserts indentations into the text
     * @param text
     * @return
     */
    private String prettyPrint (String text) {
    	StringBuffer result = new StringBuffer();
    	String line;
    	int indentLevel = 0;
    	BufferedReader reader = new BufferedReader(new StringReader(text));
    	try {
        	reader.readLine(); //hack to remove first line
			line = reader.readLine();
			while (line != null) {	
				if (line.startsWith("</") ) {
					indentLevel--;
					for (int i=0; i < indentLevel; i++) {
						result.append("\t");
					}
				} 

				else if (line.startsWith("<")) {
					for (int i=0; i < indentLevel; i++) {
						result.append("\t");
					}
					if (!line.contains("</") ) {
						indentLevel++;
					}	
				} else {
					for (int i=0; i < indentLevel; i++) {
						result.append("\t");
					}
				}
				result.append(line + "\n");
				if (line.contains("/>")) {
					indentLevel--;				
				}
				line = reader.readLine();
			}
    	} catch (IOException e) {
    		FMCorePlugin.getDefault().logError(e);
		}
    	return result.toString();
    }
    
    public String writeToString() {
    	//Create Empty DOM Document
    	DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        dbf.setNamespaceAware(true);
        dbf.setIgnoringComments(true);
        dbf.setIgnoringElementContentWhitespace(false);
		dbf.setCoalescing(true);
		dbf.setExpandEntityReferences(true);
		DocumentBuilder db = null;
		try {
		    db = dbf.newDocumentBuilder();
		} catch (ParserConfigurationException pce) {
			FMCorePlugin.getDefault().logError(pce);
		}
		Document doc = db.newDocument();
		//Create the Xml Representation
		createXmlDoc(doc);
		
		//Transform the Xml Representation into a String
		Transformer transfo = null;
		try {
			transfo = TransformerFactory.newInstance().newTransformer();
		} catch (TransformerConfigurationException e) {
			FMCorePlugin.getDefault().logError(e);
		} catch (TransformerFactoryConfigurationError e) {
			FMCorePlugin.getDefault().logError(e);
		}
		
		transfo.setOutputProperty(OutputKeys.METHOD, "xml");
		transfo.setOutputProperty(OutputKeys.INDENT, "yes");
		StreamResult result = new StreamResult(new StringWriter());
		DOMSource source = new DOMSource(doc);
		try {
			transfo.transform(source, result);
		} catch (TransformerException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		
		return prettyPrint(result.getWriter().toString()); 
	}    
}
