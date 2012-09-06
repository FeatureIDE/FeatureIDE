/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.fm.core.io.xml;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.Collection;
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

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Text;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelWriter;


/**
 * Prints a feature model in XML format.
 * 
 * @author Fabian Wielgorz -> OLD
 * @author Dariusz Krolikowski
 * @author Maik Lampe
 * 
 */
public class XmlFeatureModelWriter extends AbstractFeatureModelWriter {
	
	/**
	 * Creates a new writer and sets the feature model to write out.
	 * 
	 * @param featureModel the structure to write
	 */
	public XmlFeatureModelWriter(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
	/**
	 * Creates XML-Document
	 * @param doc document to write
	 */
    protected void createXmlDoc(Document doc) {
        Element root = doc.createElement("featureModel");
    	Element struct = doc.createElement("struct");
    	Element constraints = doc.createElement("constraints");
    	Element comments = doc.createElement("comments");
    	Element order = doc.createElement("featureOrder");
    	
    	root.setAttribute("chosenLayoutAlgorithm", ""+featureModel.getLayout().getLayoutAlgorithm());
    	
    	if(featureModel.getLayout().verticalLayout() && !featureModel.getLayout().hasFeaturesAutoLayout()){
    		root.setAttribute("horizontalLayout", "true");
		}
    	if(!featureModel.getLayout().showHiddenFeatures()){
    		root.setAttribute("showHiddenFeatures", "false");
    	}
    	
    	doc.appendChild(root);
    	root.appendChild(struct);
    	createXmlDocRec(doc, struct, featureModel.getRoot());
    	
    	root.appendChild(constraints);
    	for(int i = 0; i < featureModel.getConstraints().size(); i++){
        	Element rule;
        	rule = doc.createElement("rule");
        	if(!featureModel.getLayout().hasFeaturesAutoLayout()){
        		   rule.setAttribute("coordinates", 
                   		""+featureModel.getConstraints().get(i).getLocation().x+"," 
                   		+" "+featureModel.getConstraints().get(i).getLocation().y);
        	}
         
           
        	constraints.appendChild(rule);
    		createPropositionalConstraints(doc, rule, featureModel.getConstraints().get(i).getNode());	
    	}
    	
    	root.appendChild(comments);
    	for(int i=0; i<featureModel.getComments().size(); i++){
        	Element c;
        	c = doc.createElement("c");
        	comments.appendChild(c);	
        	
        	Text text = doc.createTextNode(featureModel.getComments().get(i));
        	c.appendChild(text);
        }
    	order.setAttribute("userDefined", Boolean.toString(featureModel.isFeatureOrderUserDefined()));
    	root.appendChild(order);
    	
    	if (featureModel.isFeatureOrderUserDefined()) {
	    	Collection<String> featureOrderList = featureModel.getFeatureOrderList();
	    	
	    	if (featureOrderList.isEmpty())
	    		featureOrderList = featureModel.getConcreteFeatureNames();
	    	
	    	for(String featureName : featureOrderList){
	    		Element feature = doc.createElement("feature");
	    		feature.setAttribute("name", featureName);
	    		order.appendChild(feature);
	    	}
    	}
    }
    
    /**
     * Creates document based on feature model step by step
     * @param doc document to write
     * @param node parent node
     * @param feat current feature
     */
    private void createXmlDocRec(Document doc, Element node, Feature feat) {

    	if (feat == null) return;
    	
    	Element fnod;
    	LinkedList<Feature> children;
    	
    	children = feat.getChildren();
    	if (children.isEmpty()) {
    		fnod = doc.createElement("feature");
    		
    		writeAttributes(node, fnod, feat);
    	}
    	else{
    		if (feat.isAnd()) {
    			fnod = doc.createElement("and");
    		} else if (feat.isOr()) {
    			fnod = doc.createElement("or");
    		} else if (feat.isAlternative()) {
    			fnod = doc.createElement("alt");
	    	} else fnod = doc.createElement("unknown");//FMCorePlugin.getDefault().logInfo("creatXMlDockRec: Unexpected error!");
	    	
    		writeAttributes(node, fnod, feat);
	    	
	    	Iterator<Feature> i = children.iterator();
	    	while (i.hasNext()) {
	    		createXmlDocRec(doc, fnod ,i.next());
	    	}
    	}
    }
    
    private void writeAttributes(Element node, Element fnod, Feature feat) {
    	fnod.setAttribute("name", feat.getName());
		if(feat.isHidden())		fnod.setAttribute("hidden", "true");
    	if(feat.isMandatory())	fnod.setAttribute("mandatory", "true");
    	if(feat.isAbstract())	fnod.setAttribute("abstract", "true");
    	
    	if(!featureModel.getLayout().showHiddenFeatures() || !featureModel.getLayout().hasFeaturesAutoLayout()) 
    		fnod.setAttribute("coordinates", +feat.getLocation().x
    				+", "+feat.getLocation().y);
    	
    	node.appendChild(fnod);
    }
  
    /**
     * Inserts the tags concerning propositional constraints into the DOM 
     * document representation
     * @param doc
     * @param FeatMod Parent node for the propositonal nodes
     */
    private void createPropositionalConstraints(Document doc, Element xmlNode, org.prop4j.Node node ) {

    	if (node == null) return;

    	String clss = node.getClass().getName();
    	Element op; 
    	
    	if (clss.equals("org.prop4j.Literal")){
    		op = doc.createElement("var");
    		xmlNode.appendChild(op);
    		Text text = doc.createTextNode(node.toString());
    		op.appendChild(text);
    		return;
    	}
    	
    	if (clss.equals("org.prop4j.And")){
    		op = doc.createElement("conj");
    		xmlNode.appendChild(op);
    	}
    	else if (clss.equals("org.prop4j.Or")){
    		op = doc.createElement("disj");
    		xmlNode.appendChild(op);
    	}
    	else if (clss.equals("org.prop4j.Not")){
    		op = doc.createElement("not");
    		xmlNode.appendChild(op);
    	}
    	else if (clss.equals("org.prop4j.Equals")){
    		op = doc.createElement("eq");
    		xmlNode.appendChild(op);
    	}

    	else if (clss.equals("org.prop4j.Implies")){
    		op = doc.createElement("imp");
    		xmlNode.appendChild(op);
    	}
    	else if (clss.equals("org.prop4j.AtMost")){
    		op = doc.createElement("atmost1");
    		xmlNode.appendChild(op);
    	}
    	else{
    		op = doc.createElement("unknown");
    		xmlNode.appendChild(op);
    	}
    	
    	org.prop4j.Node[] children = node.getChildren();
    	
    	for(int i=0; i<children.length; i++){
    		createPropositionalConstraints(doc, op, children[i]);
    	}
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
