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
package featureide.fm.core.io.xml;

import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.Scanner;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.prop4j.And;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Not;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.AbstractFeatureModelReader;
import featureide.fm.core.io.UnsupportedModelException;

/**
 * TODO description
 * 
 * @author Fabian Wielgorz
 */
public class XmlFeatureModelReader extends AbstractFeatureModelReader {
	
	/**
	 * Creates a new reader and sets the feature model to store the data.
	 * 
	 * @param featureModel the structure to fill
	 */
	public XmlFeatureModelReader(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
	/**
	 * Searches the Document tree for the first ancestor that is either the
	 * Xml-Tag MFeature or Feature
	 * @param n Startnode
	 * @return Node containing parent feature or null if there isn't one
	 * @throws UnsupportedModelException
	 */
    private Node findParentFeature(Node n) throws UnsupportedModelException {
    	Node wNode = n.getParentNode();
    	while (wNode != null) {
    		if (wNode.getNodeType() == Node.ELEMENT_NODE) {
    			String tag = wNode.getNodeName();
    	    	if (tag.equals("MFeature") || tag.equals("Feature")) {
    	    		return wNode;
    	    	} else if (tag.equals("FeatureModel")) return null;
    		}
    		wNode = wNode.getParentNode();
    	}
    	return null;
    }
    
    /**
     * Finds the Name, contained in a Name-Tag for a given Feature
     * @param n Node that is either the Xml-Tag MFeature or Feature
     * @return Name string
     * @throws UnsupportedModelException
     */
    private String getFeatureName(Node n) throws UnsupportedModelException {
    	String result = null;
    	Node wNode;
    	NodeList children = n.getChildNodes();
    	NodeList grandchildren;
    	for (int i=0; i < children.getLength(); i++) {
    		wNode = children.item(i);
    		if ((wNode.getNodeType() == Node.ELEMENT_NODE) 
    				&& wNode.getNodeName().equals("Name")) {
    			grandchildren = wNode.getChildNodes();
        		for (int j=0; j < grandchildren.getLength(); j++) {
        			result = grandchildren.item(j).getNodeValue();
            		if (result != null) return result;
        		}
    		}
    	}
    	throw new UnsupportedModelException("No Name-Tag found" +
    										" for this Feature", 0);
	}
                
    @Override
    protected void parseInputStream(InputStream inputStream)
							throws UnsupportedModelException {
    	warnings.clear();
        //Parse the XML-File to a DOM-Document
    	boolean ignoreWhitespace = true;
        boolean ignoreComments = true;
        boolean putCDATAIntoText = true;
        boolean createEntityRefs = false;
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        dbf.setNamespaceAware(true);
        dbf.setIgnoringComments(ignoreComments);
        dbf.setIgnoringElementContentWhitespace(ignoreWhitespace);
        dbf.setCoalescing(putCDATAIntoText);
        dbf.setExpandEntityReferences(!createEntityRefs);
        DocumentBuilder db = null;
        try {
            db = dbf.newDocumentBuilder();
        } catch (ParserConfigurationException pce) {
            System.err.println(pce);
            System.exit(1);
        }
        Document doc = null;
        try {
            doc = db.parse(inputStream);
        } catch (SAXException se) {
            System.err.println(se.getMessage());
            System.exit(1);
        } catch (IOException ioe) {
            System.err.println(ioe);
            System.exit(1);
        }
        // Create the Feature Model from the DOM-Document
		buildFeatureModel(doc);
    }
    
    /**
     * Handles the Xml-Tags concerning the type of connection between Features
     * @param n
     * @throws UnsupportedModelException
     */
    private void handleConnectionTags(Node n) throws UnsupportedModelException {
    	String tag = n.getNodeName();
    	Feature feat;
    	Node wNode;
    	if (tag.equals("And")) {
			wNode = findParentFeature(n);
			feat = featureModel.getFeature(getFeatureName(wNode));
			if (feat == null) throw new UnsupportedModelException("Connection" +
					" does not have a parent", 0);
			feat.changeToAnd();
    	} else if (tag.equals("Or")) {
			wNode = findParentFeature(n);
			feat = featureModel.getFeature(getFeatureName(wNode));
			if (feat == null) throw new UnsupportedModelException("Connection" +
					" does not have a parent", 0);
			feat.changeToOr();
    	} else if (tag.equals("Alternative")) {
			wNode = findParentFeature(n);
			feat = featureModel.getFeature(getFeatureName(wNode));
			if (feat == null) throw new UnsupportedModelException("Connection" +
					" does not have a parent", 0);
			feat.changeToAlternative();
    	} else if (tag.equals("PropositionalConstraints")) {
    		
    	} else if (tag.equals("PConstraint")) {
    		handlePropConst(n);
    	} else if (tag.equals("Annotations")) {
    		handleAnnotations(n);
    	} else if (tag.equals("Name")) {
    		return;
    	} else if (tag.equals("FeatureModel")) {
    		return;
    	} else {
    		throw new UnsupportedModelException("Unknown Xml-Tag found", 0);
    	}
    }
    
    /**
     * Handles the Propositional Constraint found in a PConstraint xml-tag
     * @param n
     */
    private void handlePropConst(Node n) {
    	NodeList nodelist = n.getChildNodes();
    	for (int i=0; i<nodelist.getLength();i++) {
    		Node node = nodelist.item(i);
    		if (node.getNodeType() == Node.TEXT_NODE) {
    			Scanner scan = new Scanner(node.getNodeValue());
    			String str;
    			LinkedList<String> elements = new LinkedList<String>();
    			while (scan.hasNext()) {
    				str = scan.next();
    				if (str.startsWith("(")) {
	    				while (str.startsWith("(")) {
	    					elements.addLast("(");
	    					str = str.substring(1);
	    				} 
	    				elements.addLast(str);
    				} else if (str.contains(")")) {
        				elements.addLast(str.substring(0, str.indexOf(")")));
        				str = str.substring(str.indexOf(")"));
        				while (str.contains(")")) {
        					elements.addLast(")");
        					str = str.substring(1);
        				}
    				} else {
    					elements.addLast(str);
    				}   				
    			}
    			// Shouldn't be needed
     			//elements = insertBrackets(elements);  
    			try {
    				org.prop4j.Node propNode = buildPropNode(elements);
    				featureModel.addPropositionalNode(propNode);
				} catch (UnsupportedModelException e) {
					e.printStackTrace();
				}
    		}
    	}
    	
    }
    
    private void handleAnnotations(Node n) {
    	String result = "";
    	Node wNode;
    	NodeList children = n.getChildNodes();
    	for (int i=0; i < children.getLength(); i++) {
    		wNode = children.item(i);
    		if (wNode.getNodeType() == Node.TEXT_NODE) {
    			result = result + wNode.getNodeValue();
    		}
    	}
    	featureModel.setAnnotations(result);
    }
    
    /**
     * Inserts missing brackets in left-associative way
     * @param list Boolean expression
     * @return Boolean expression with the full set of brackets
     */
    @SuppressWarnings("unused")
	private LinkedList<String> insertBrackets(LinkedList<String> list) {
    	LinkedList<String> result = new LinkedList<String>();
    	LinkedList<Integer> bracketList = new LinkedList<Integer>();
    	bracketList.addFirst(0);
    	int indexCount = 0;
    	int countBoolOps = 0;
    	String element;
    	while (!list.isEmpty()) {
    		element = list.remove();
    		result.add(element);
    		if (element.equals("(")) {
    			countBoolOps = 0;
    			bracketList.addFirst(indexCount);
    		}
    		if (element.equals(")")) {
    			countBoolOps = 0;
    			bracketList.removeFirst();
    		}
    		if ((element.equals("and")) || (element.equals("or")) || 
    				(element.equals("implies")) || (element.equals("iff"))) {
    			if (countBoolOps == 0) {
    				countBoolOps++;
    			} else {
    				if ((!list.isEmpty()) && (!list.getFirst().equals(")"))) {
    					result.add(bracketList.getFirst(), "(");
    					result.add(result.size() - 1, ")");
    				}
    			}
    		}
    		indexCount++;
    	}
    	return result;
    }
    
    /**
     * Builds a Propositional Node from a propositional formula
     * @param list
     * @return
     * @throws UnsupportedModelException
     */
    private org.prop4j.Node buildPropNode(LinkedList<String> list) 
    		throws UnsupportedModelException {
    	LinkedList<String> left = new LinkedList<String>();
    	org.prop4j.Node leftResult, rightResult;
    	int bracketCount = 0;
    	String element;
    	while (!list.isEmpty()) {
    		element = list.removeFirst();
    		if (element.equals("(")) bracketCount++;
    		if (element.equals(")")) bracketCount--;
    		if ((element.equals("not")) && (list.getFirst().equals("(")) 
    									&& (list.getLast().equals(")"))) {
    			list.removeFirst();
				list.removeLast();
				return new Not(buildPropNode(list));
    		}
    		if ((element.equals("and")) || (element.equals("or")) || 
    				(element.equals("implies")) || (element.equals("iff")) ) {
    			if (bracketCount == 0) {
    				if ((left.getFirst().equals("(")) && 
    						(left.getLast().equals(")"))) {
    					left.removeFirst();
    					left.removeLast();
    				}
    				leftResult = buildPropNode(left);
    				if ((list.getFirst().equals("(")) && 
    						(list.getLast().equals(")"))) {
    					list.removeFirst();
    					list.removeLast();
    				}
    				rightResult = buildPropNode(list);
    				if (element.equals("and")) 
    					return new And(leftResult, rightResult);
    				if (element.equals("or")) 
    					return new Or(leftResult, rightResult);
    				if (element.equals("implies")) 
    					return new Implies(leftResult, rightResult);
    				if (element.equals("iff")) 
    					return new Equals(leftResult, rightResult);
    			}
    		}
    		left.add(element);    		
    	}
    	return buildLeafNodes(left);
    }
    
    private org.prop4j.Node buildLeafNodes(LinkedList<String> list) 
    		throws UnsupportedModelException {
    	String element;
    	if (list.isEmpty()) 
    		throw new UnsupportedModelException("Fehlendes Element", 0);
		element = list.removeFirst();
		if (element.equals("not")) {
			return new Not(buildPropNode(list));
		} else {
			if (featureModel.getFeature(element) == null)
				throw new UnsupportedModelException("The feature '" + element + 
						"' does not occur in the grammar!", 0);			
			return new Literal(element);
		}
    }
    
    
    /**
     * Processes a single Xml-Tag.
     * @param n
     * @throws UnsupportedModelException
     */
    private void buildFModelStep(Node n) throws UnsupportedModelException {
    	Feature feat;
    	if (n.getNodeType() != Node.ELEMENT_NODE) return;
    	String tag = n.getNodeName();
    	if (tag.equals("MFeature")) {
    		feat = new Feature(featureModel);
    		feat.setMandatory(true);
    	} else if (tag.equals("Feature")) {
    		feat = new Feature(featureModel);
    		feat.setMandatory(false);
    	} else {
    		handleConnectionTags(n);
    		return;
    	}
    	feat.setName(getFeatureName(n));
		Node wNode = findParentFeature(n);
		if (wNode != null) {
			Feature tmpFeat = featureModel.getFeature(getFeatureName(wNode));
    		feat.setParent(tmpFeat);
    		tmpFeat.addChild(feat);
		} else featureModel.setRoot(feat);
		featureModel.addFeature(feat);
    }
    
    /**
     * Initialize the build process.
     * @param doc Document from which the Feature Model is build
     * @throws UnsupportedModelException
     */
    private void buildFeatureModel(Document doc) 
    			throws UnsupportedModelException {
    	featureModel.reset();
    	featureModel.hasAbstractFeatures(false);
    	buildFModelRec(doc);   	 	
    }
    
    /**
     * Recursively traverses the Document structure
     * @param n
     * @throws UnsupportedModelException
     */
    private void buildFModelRec(Node n) throws UnsupportedModelException {
    	buildFModelStep(n);
    	for (Node child = n.getFirstChild(); child != null;
					child = child.getNextSibling()) {
    		buildFModelRec(child);
    	}
    }
    
    
    
}
