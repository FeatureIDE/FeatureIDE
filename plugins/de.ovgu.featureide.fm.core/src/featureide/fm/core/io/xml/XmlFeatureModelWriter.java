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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.Iterator;
import java.util.LinkedList;

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

import org.prop4j.NodeWriter;
import org.w3c.dom.Document;
import org.w3c.dom.Node;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.AbstractFeatureModelWriter;

/**
 * TODO description
 * 
 * @author Fabian Wielgorz
 */
public class XmlFeatureModelWriter extends AbstractFeatureModelWriter {
		
	public XmlFeatureModelWriter() {
		
	}
	
	/**
	 * Creates a new writer and sets the feature model to write out.
	 * 
	 * @param featureModel the structure to write
	 */
	public XmlFeatureModelWriter(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
    /**
     * Creates the DOM Document Representation from the feature model fmodel
     * by using createXmlDocRec
     * @param doc Document where the feature model is put
     */
    private void createXmlDoc(Document doc) {
        Node elem = doc.createElement("FeatureModel");
    	doc.appendChild(elem);
    	createXmlDocRec(doc, elem, featureModel.getRoot());
    	createPropositionalConstraints(doc, elem);
    	createAnnotations(doc, elem);
    }
    
    /**
     * Creates the DOM Document Representation from the feature model fmodel
     * by recursively building the Nodes
     * @param doc Document where the feature model is put
     * @param nod Current Node in the Document Tree
     * @param feat Current Feature in the feature model Tree
     */
    private void createXmlDocRec(Document doc, Node nod, Feature feat) {
    	Node nnod, fnod, tnod;
    	LinkedList<Feature> children;
    	if (feat == null) return;
    	fnod = (feat.isMandatory())? doc.createElement("MFeature") 
    							   : doc.createElement("Feature");
    	nod.appendChild(fnod);
    	nnod = doc.createElement("Name");
    	fnod.appendChild(nnod);
    	tnod = doc.createTextNode(feat.getName());
    	nnod.appendChild(tnod);
    	children = feat.getChildren();
    	if (children.isEmpty()) return;
    	if (feat.isAnd()) {
    		nnod = doc.createElement("And");
    	} else if (feat.isOr()) {
    		nnod = doc.createElement("Or");
    	} else if (feat.isAlternative()) {
    		nnod = doc.createElement("Alternative");
    	} else System.out.println("creatXMlDockRec: Unexpected error!");
    	fnod.appendChild(nnod);
    	Iterator<Feature> i = children.iterator();
    	while (i.hasNext()) {
    		createXmlDocRec(doc, nnod ,i.next());
    	}
    }
    
    /**
     * Inserts the tags concerning propositional constraints into the DOM 
     * document representation
     * @param doc
     * @param FeatMod Parent node for the propositonal nodes
     */
    private void createPropositionalConstraints(Document doc, Node FeatMod) {
    	if (featureModel.getPropositionalNodes().isEmpty())
			return;
    	Node propConstr = doc.createElement("PropositionalConstraints");
    	Node newNode, pConstr; 
		FeatMod.appendChild(propConstr);
		newNode = doc.createTextNode("\n");
		propConstr.appendChild(newNode);
		for (org.prop4j.Node node : featureModel.getPropositionalNodes()) {
			pConstr = doc.createElement("PConstraint");
			propConstr.appendChild(pConstr);
			String nodeString = NodeWriter.nodeToString(node, 
					NodeWriter.textualSymbols, true);
			if ((nodeString.startsWith("(")) && (nodeString.endsWith(")"))) {
				nodeString = nodeString.substring(1, nodeString.length() - 1);
			}
			newNode = doc.createTextNode(nodeString);
			pConstr.appendChild(newNode);
		}
	}
    
    private void createAnnotations(Document doc, Node FeatMod) {
    	String annotationText = featureModel.getAnnotations();
    	if (annotationText == null)
			return;
    	Node annotations = doc.createElement("Annotations");
    	Node newNode; 
		FeatMod.appendChild(annotations);
		newNode = doc.createTextNode("\n" + annotationText + "\n");
		annotations.appendChild(newNode);
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
			line = reader.readLine();
			while (line != null) {	
				if (line.startsWith("</")) {
					indentLevel--;
					for (int i=0; i < indentLevel; i++) {
						result.append("   ");
					}
				} else if (line.startsWith("<")) {
					for (int i=0; i < indentLevel; i++) {
						result.append("   ");
					}
					if (!line.contains("</")) {
						indentLevel++;
					}	
				} else {
					for (int i=0; i < indentLevel; i++) {
						result.append("   ");
					}
				}
				result.append(line + "\n");
				line = reader.readLine();
			}
    	} catch (IOException e) {
			e.printStackTrace();
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
		    System.err.println(pce);
		    System.exit(1);
		}
		Document doc = db.newDocument();
		//Create the Xml Representation
		createXmlDoc(doc);
		
		//Transform the Xml Representation into a String
		Transformer transfo = null;
		try {
			transfo = TransformerFactory.newInstance().newTransformer();
		} catch (TransformerConfigurationException e) {
			e.printStackTrace();
		} catch (TransformerFactoryConfigurationError e) {
			e.printStackTrace();
		}
		transfo.setOutputProperty(OutputKeys.METHOD, "xml");
		transfo.setOutputProperty(OutputKeys.INDENT, "yes");
		StreamResult result = new StreamResult(new StringWriter());
		DOMSource source = new DOMSource(doc);
		try {
			transfo.transform(source, result);
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		return prettyPrint(result.getWriter().toString());
	}    
}
