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
package de.ovgu.featureide.fm.core.io.splconquerer;

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
 * Prints a feature model in SPLConqueror format.
 * 
 * @author Dariusz Krolikowski
 * @author Maik Lampe
 * @author Thomas Thuem
 */
public class ConquererFMWriter extends AbstractFeatureModelWriter {
	
	/**
	 * Creates a new writer and sets the feature model to write out.
	 * 
	 * @param featureModel the structure to write
	 */
	public ConquererFMWriter(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
	private Map<String,Set<String>> require, exclude;
	
	/**
	 * Creates XML-Document
	 * @param doc document to write
	 */
    private void createXmlDoc(Document doc) {
        Element plm = doc.createElement("plm");
    	doc.appendChild(plm);
		plm.setAttribute("name", featureModel.getRoot().getName());
		plm.setAttribute("canReuseInstance", "true");
		
		require = new HashMap<String, Set<String>>();
		exclude = new HashMap<String, Set<String>>();
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
        					Set<String> set = require.get(literalA.var);
        					if (set == null) {
        						set = new HashSet<String>();
        						require.put(literalA.var.toString(), set);
        					}
        					set.add(literalB.var.toString());
        				}
        				else {
        					Set<String> set = exclude.get(literalA.var);
        					if (set == null) {
        						set = new HashSet<String>();
        						exclude.put(literalA.var.toString(), set);
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

    	initializeIDs();
       	generateSubtree(doc, plm, featureModel.getRoot());
    	
    	plm.appendChild(doc.createElement("properties"));

    	Element furtherConstraints = doc.createElement("furtherConstraints");
    	plm.appendChild(furtherConstraints);
    	for (Node child : furtherNodes) {
			Element clause = doc.createElement("clause");
			furtherConstraints.appendChild(clause);
			clause.appendChild(doc.createTextNode(child.toString()));
		}
    }
    
    private void generateSubtree(Document doc, Element node, Feature feature) {
    	if (!feature.isRoot())
    		generateElement(doc, node, feature);
    	
    	for (Feature child : feature.getChildren())
    		generateSubtree(doc, node, child);
    }
  
	private void generateElement(Document doc, Element node, Feature feature) {
    	Element element = doc.createElement("element");
    	node.appendChild(element);
		element.setAttribute("id", getID(feature.getName()));
		element.setAttribute("name", feature.getName());
		element.setAttribute("type", "feature");
		element.setAttribute("optional", feature.isMandatory() ? "false" : "true");
		element.setAttribute("dynamic", "false");
    	
    	element.appendChild(doc.createElement("path_absolut"));
    	element.appendChild(doc.createElement("path_relativ"));

    	if (!feature.getParent().isRoot()) {
        	Element parentElement = doc.createElement("parentElement");
        	element.appendChild(parentElement);
        	Element id = doc.createElement("id");
        	parentElement.appendChild(id);
        	id.appendChild(doc.createTextNode(getID(feature.getParent().getName())));
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
	            	id.appendChild(doc.createTextNode(getID(childFeature.getName())));
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
	            	id.appendChild(doc.createTextNode(getID(childFeature.getName())));
	            	Element name = doc.createElement("name");
	            	constraint_element.appendChild(name);
	            	name.appendChild(doc.createTextNode(childFeature.getName()));
	    		}
    	}

    	Element requires = doc.createElement("constraint");
    	constraints.appendChild(requires);
    	requires.setAttribute("type", "requires");
    	Set<String> requireFeature = require.get(feature.getName());
    	if (requireFeature != null)
	    	for (String childFeature : requireFeature) {
	        	Element constraint_element = doc.createElement("constraint_element");
	        	requires.appendChild(constraint_element);
	        	Element id = doc.createElement("id");
	        	constraint_element.appendChild(id);
	        	id.appendChild(doc.createTextNode(getID(childFeature)));
	        	Element name = doc.createElement("name");
	        	constraint_element.appendChild(name);
	        	name.appendChild(doc.createTextNode(childFeature));
			}

    	Element excludes = doc.createElement("constraint");
    	constraints.appendChild(excludes);
    	excludes.setAttribute("type", "excludes");
    	Set<String> excludeFeature = exclude.get(feature.getName());
    	if (excludeFeature != null)
	    	for (String childFeature : excludeFeature) {
	        	Element constraint_element = doc.createElement("constraint_element");
	        	excludes.appendChild(constraint_element);
	        	Element id = doc.createElement("id");
	        	constraint_element.appendChild(id);
	        	id.appendChild(doc.createTextNode(getID(childFeature)));
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
        	id.appendChild(doc.createTextNode(getID(childFeature.getName())));
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
    	StringBuilder result = new StringBuilder();
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
						result.append('\t');
					}
				} 

				else if (line.startsWith("<")) {
					for (int i=0; i < indentLevel; i++) {
						result.append('\t');
					}
					if (!line.contains("</") ) {
						indentLevel++;
					}	
				} else {
					for (int i=0; i < indentLevel; i++) {
						result.append('\t');
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
    
    private HashMap<String,Integer> ids;
    
    private void initializeIDs() {
    	ids = new HashMap<String, Integer>();
    	initializeIDs(featureModel.getRoot());
    }
    
    private void initializeIDs(Feature feature) {
    	getID(feature.getName());
    	for (Feature child : feature.getChildren())
    		initializeIDs(child);
    }
    
    private String getID(String feature) {
    	Integer id = ids.get(feature);
    	if (id != null)
    		return id.toString();
    	id = ids.size() + 1;
    	ids.put(feature, id);
    	return id.toString();
    }
    
}
