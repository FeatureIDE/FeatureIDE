/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.core.io.waterloo;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.util.Arrays;
import java.util.Hashtable;
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

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;


/**
 * Parses feature model files in the Waterloo format.
 * 
 * @author Fabian Wielgorz
 */
public class WaterlooReader extends AbstractFeatureModelReader {
	
	private int line;
	
	private Hashtable<String, Feature> idTable;
	
	/**
	 * Creates a new reader and sets the feature model to store the data.
	 * 
	 * @param featureModel the structure to fill
	 */
	public WaterlooReader(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
	@Override
    protected void parseInputStream(InputStream inputStream)
							throws UnsupportedModelException {
    	warnings.clear();
        //Parse the XML-File to a DOM-Document
    	boolean ignoreWhitespace = false;
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
            FMCorePlugin.getDefault().logError(pce);
        }
        Document doc = null;
        try {
            doc = db.parse(inputStream);
        } catch (SAXException se) {
            FMCorePlugin.getDefault().logError(se);
        } catch (IOException ioe) {
            FMCorePlugin.getDefault().logError(ioe);
        }       
        featureModel.reset();
    	line = 0;
    	idTable = new Hashtable<String, Feature>();
    	// Create the Feature Model from the DOM-Document
    	buildFModelRec(doc); 
    	featureModel.handleModelDataLoaded();
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
    
    /**
     * Processes a single Xml-Tag.
     * @param n
     * @throws UnsupportedModelException
     */
    private void buildFModelStep(Node n) throws UnsupportedModelException {
    	if (n.getNodeType() != Node.ELEMENT_NODE) return;
    	String tag = n.getNodeName();
    	if (tag.equals("feature_tree")) {
			handleFeatureTree(n);
    	} else if (tag.equals("feature_model")) {
    		line++;
    		return;
    	} else if (tag.equals("constraints")) {
    		line++;
    		handleConstraints(n);
    	} else {
    		throw new UnsupportedModelException("Unknown Xml-Tag", line);
    	}
    }
    
    /**
     * Reads the input in the feature tree section, interprets the input line
     * by line by using buildFeatureTree
     * @param n
     * @throws UnsupportedModelException
     */
    private void handleFeatureTree(Node n) throws UnsupportedModelException {
    	NodeList children = n.getChildNodes();
    	StringBuffer buffer = new StringBuffer();
    	Node node;
    	for (int i = 0; i < children.getLength(); i++) {
    		node = children.item(i);
    		if (node.getNodeType() == Node.TEXT_NODE) {
    			buffer.append(node.getNodeValue());
    		}
    	}
    	BufferedReader reader = new BufferedReader(new StringReader(
    			buffer.toString()));
    	buildFeatureTree(reader);
    }
    
    private String removeWhitespaces(String str){
    	str = str.trim();
    	if (str.contains(" ")){
	    	String temp = str.substring(0,str.indexOf(" ")+1);
	    	str = str.substring(str.indexOf(" ") + 1);
	    	while(str.contains(" ")){
	    		str = str.substring(0,str.indexOf(" ")) + str.substring(str.indexOf(" ")+1,str.length()); 
	    	}
	    	str = temp + str;
    	}
    	return str;
    }
    
    /**
     * Reads one line of the input Text and builds the corresponding feature
     * @param reader
     * @param lastFeat
     * @throws UnsupportedModelException
     */
    private void buildFeatureTree(BufferedReader reader) throws UnsupportedModelException {
    	try {
    		FeatureIndent lastFeat = new FeatureIndent(null, -1);
    		// List of Features with arbitrary cardinalities
    		LinkedList<FeatCardinality> arbCardGroupFeats = new LinkedList<FeatCardinality>();
    		String lineText = reader.readLine();
    		line++;
    		FeatureIndent feat;
			String featId = "";   
    		while (lineText != null) {				
	    		int countIndent = 0;
				 						
				if (lineText.trim().equals("")) {
					lineText = reader.readLine();
					line++;
					continue;
				}	
				while (lineText.startsWith("\t")) {
	    			countIndent++;
	    			lineText = lineText.substring(1);
	    		}
				int relativeIndent = countIndent - lastFeat.getIndentation();
				while (relativeIndent < 1) {
//					if (lastFeat.isRoot()) throw new UnsupportedModelException(
//							"Indentation error, feature has no parent", line);
//					lastFeat = (FeatureIndent) lastFeat.getParent();
//					relativeIndent = countIndent - lastFeat.getIndentation();
					
					if (!lastFeat.isRoot()){
						lastFeat = (FeatureIndent) lastFeat.getParent();
						relativeIndent = countIndent - lastFeat.getIndentation();
					}
				}
				// Remove special characters and whitespaces from names
				lineText = removeWhitespaces(lineText);

				char[] lineTextChars = lineText.toCharArray();
				for (int i = 0; i < lineTextChars.length; i++) {
					Character c = lineTextChars[i];
					
					if (!(Character.isLetterOrDigit(c) || c.equals(':') 
							|| c.equals('[') || c.equals(']') || c.equals(',')
							|| c.equals('*') || c.equals('(') || c.equals(')'))) {
						lineTextChars[i] = '_';
					}
				}
				
				lineText = new String(lineTextChars);
				
				if (lineText.startsWith(":r")) {
					feat = new FeatureIndent(featureModel, 0);
		    		feat.setMandatory(true);
		    		featId = setNameGetID(feat, lineText);
//		    		if (feat.getName().trim().toLowerCase().equals("root"))
//		    			feat.setName("root_");
		    		featureModel.setRoot(feat);	
		    		feat.changeToAnd();
		    		countIndent = 0;
				} else if (lineText.startsWith(":m")) {
					feat = new FeatureIndent(featureModel, countIndent);
		    		feat.setMandatory(true);
		    		featId = setNameGetID(feat, lineText);
		    		feat.setParent(lastFeat);
		    		lastFeat.addChild(feat);
		    		feat.changeToAnd();
				} else if (lineText.startsWith(":o")) {
					feat = new FeatureIndent(featureModel, countIndent);
		    		feat.setMandatory(false);
		    		featId = setNameGetID(feat, lineText);
		    		feat.setParent(lastFeat);
		    		lastFeat.addChild(feat);
		    		feat.changeToAnd();
				} else if (lineText.startsWith(":g")) {
					if (lineText.contains("[1,1]")) {
						lastFeat.changeToAlternative();
					} else if (lineText.contains("[1,*]")) {
						lastFeat.changeToOr();
					} else if ((lineText.contains("[")) && (lineText.contains("]")))  {
						int index = lineText.indexOf('[');
						int start = Character.getNumericValue(lineText.charAt(index + 1));
						int end = Character.getNumericValue(lineText.charAt(index + 3));
						FeatCardinality featCard = new FeatCardinality(lastFeat, start, end);
						arbCardGroupFeats.add(featCard);
					} else throw new UnsupportedModelException("Couldn't " +
							"determine group cardinality", line);
					//lastFeat = feat;
					//featId = featId + "_ ";
					lineText = reader.readLine();
					line++;
					continue;
				} else if (lineText.startsWith(":")) {
					feat = new FeatureIndent(featureModel, countIndent);
		    		feat.setMandatory(true);
		    		String name;
		    		if (lineText.contains("(")) {
		    			name = lineText.substring(2, lineText.indexOf('('));
		        		featId = lineText.substring(lineText.indexOf('(') + 1, 
		        				lineText.indexOf(')'));
		        	} else {
		        		name = lineText.substring(2, lineText.length()); // + line;
		        		featId = name;
		        	}
	    			if (Character.isDigit(name.charAt(0))) name = "a" + name;
	        		feat.setName(name);
		    		feat.setParent(lastFeat);
		    		lastFeat.addChild(feat);
		    		feat.changeToAnd();
				} else throw new UnsupportedModelException("Couldn't match with " +
						"known Types: :r, :m, :o, :g, :", line);
				if (!featureModel.addFeature(feat)) {
					feat.setName(featId);
					featureModel.addFeature(feat);
				}

				if (idTable.containsKey(featId)) throw 
					new UnsupportedModelException("Id: " + featId + " occured" +
					" second time, but may only occur once", line);
				idTable.put(featId, feat);
				
				lastFeat = feat;
				lineText = reader.readLine();
				line++;
    		}
    		
    		handleArbitrayCardinality(arbCardGroupFeats);
		} catch (IOException e) {
			FMCorePlugin.getDefault().logError(e);
		}
    }
    
    private String setNameGetID (Feature feat, String lineText) {
    	String featId, name;    	
    	if (lineText.contains("(")) {
    		name = lineText.substring(3, lineText.indexOf('(') );
    		featId = lineText.substring(lineText.indexOf('(') + 1, 
    				lineText.indexOf(')'));
    	} else {
    		name = lineText.substring(3, lineText.length()); // + line;
    		featId = name;
    	}
    	if (Character.isDigit(name.charAt(0))) name = "a" + name;
    	feat.setName(name);
    	return featId;
    }
    
    /**
     * If there are groups with a cardinality other then [1,*] or [1,1], this
     * function makes the necessary adjustments to the model 
     * @param featList List of features with arbitrary cardinalities
     * @throws UnsupportedModelException
     */
    private void handleArbitrayCardinality(LinkedList<FeatCardinality> featList) 
    		throws UnsupportedModelException {
    	org.prop4j.Node node;
    	for (FeatCardinality featCard : featList) {   		
    		Feature feat = featCard.feat;
    		node = new And();    		
    		LinkedList<Feature> children = feat.getChildren();
    		for (Feature child : children) child.setMandatory(false);
    		int start = featCard.start;
    		int end = featCard.end;
    		if ((start < 0) || (start > end) || (end > children.size())) 
    			throw new UnsupportedModelException("Group cardinality " +
					"invalid", line);
    		int f = children.size();
    		node = buildMinConstr(children, f - start + 1, feat.getName());
    		featureModel.addPropositionalNode(node);
    		if ((start > 0) && (end < f)) {
    			node = buildMaxConstr(children, end + 1);
    			featureModel.addPropositionalNode(node);
    		}
    	}
    }
    
    /**
     * Builds the propositional constraint, denoting a minimum of features has
     * to be selected
     * @param list
     * @param length
     * @param parentName
     * @return
     */
    private org.prop4j.Node buildMinConstr (LinkedList<Feature> list, int length, 
    		String parentName) {
    	LinkedList<org.prop4j.Node> result = new LinkedList<org.prop4j.Node>();
    	LinkedList<org.prop4j.Node> partResult = new LinkedList<org.prop4j.Node>();
    	int listLength = list.size();
    	int[] indexes = new int[length];
    	int[] resIndexes =  new int[length];
    	for (int i = 0; i < length; i++) {
    		indexes[i] = i;
    		resIndexes[i] = i + (listLength - length);
    	} 
    	while (!Arrays.equals(indexes, resIndexes)) {    		
    		partResult.add(new Literal(parentName, false));
    		for (int i = 0; i < length; i++) {
        			partResult.add(new Literal(list.get(indexes[i]).getName())); 
    		}
    		result.add(new Or(partResult));
    		for (int i = length - 1; i >= 0; i--) {
    			if (indexes[i] >= resIndexes[i]) {
    				continue;
    			}
    			indexes[i] = indexes[i] + 1;
    			for (int j = i + 1; j < length; j++) {
    				indexes[j] = indexes[j-1] + 1;
    			}
    			break;
    		}
    	}
    	partResult.add(new Literal(parentName, false));
    	for (int i = 0; i < length; i++) {
			partResult.add(new Literal(list.get(indexes[i]).getName()));
		}
		result.add(new Or(partResult));
    	return new And(result);
    }
    
    /**
     * Builds the propositional constraint, denoting a maximum of features can
     * be selected
     * @param list
     * @param length
     * @return
     */
    private org.prop4j.Node buildMaxConstr (LinkedList<Feature> list, int length) {
       	LinkedList<org.prop4j.Node> result = new LinkedList<org.prop4j.Node>();
    	LinkedList<org.prop4j.Node> partResult = new LinkedList<org.prop4j.Node>();
    	int listLength = list.size();
    	int[] indexes = new int[length];
    	int[] resIndexes =  new int[length];
    	for (int i = 0; i < length; i++) {
    		indexes[i] = i;
    		resIndexes[i] = i + (listLength - length);
    	} 
    	while (!Arrays.equals(indexes, resIndexes)) {    		
    		for (int i = 0; i < length; i++) {
        			partResult.add(new Literal(list.get(indexes[i]).getName(),
						false)); 
    		}
    		result.add(new Or(partResult));
    		for (int i = length - 1; i >= 0; i--) {
    			if (indexes[i] >= resIndexes[i]) {
    				continue;
    			}
    			indexes[i] = indexes[i] + 1;
    			for (int j = i + 1; j < length; j++) {
    				indexes[j] = indexes[j-1] + 1;
    			}
    			break;
    		}
    	}
    	for (int i = 0; i < length; i++)
    		partResult.add(new Literal(list.get(indexes[i]).getName(), false)); 
		result.add(new Or(partResult));
    	return new And(result);
    }
    
    /**
     * Handles the constraints found in the 'constraints' xml-tag
     * @param n
     * @throws UnsupportedModelException 
     */
    private void handleConstraints(Node n) throws UnsupportedModelException {
    	NodeList children = n.getChildNodes();
    	StringBuffer buffer = new StringBuffer();
    	String lineText;
    	Node node;
    	for (int i = 0; i < children.getLength(); i++) {
    		node = children.item(i);
    		if (node.getNodeType() == Node.TEXT_NODE) {
    			buffer.append(node.getNodeValue());
    		}
    	}
    	BufferedReader reader = new BufferedReader(new StringReader(
    			buffer.toString()));
    	try {
    		lineText = reader.readLine();
    		line++;
    		while (lineText != null) {    			
    			if (!lineText.trim().equals("")) {
    				handleSingleConstraint(lineText);
    			}
    			lineText = reader.readLine();
    			line++;
    		}
    	} catch (IOException e) {
    		FMCorePlugin.getDefault().logError(e);
		}
    }
    
    /**
     * Handles a single constraints.
     * @param lineText Text description of a Constraint
     * @throws UnsupportedModelException 
     */
    private void handleSingleConstraint(String lineText) 
    		throws UnsupportedModelException {
		String newLine = lineText.replace("(", " ( ");
		newLine = newLine.replace(")", " ) ");
		newLine = newLine.replace("~", " ~ ");
    	Scanner scan = new Scanner(newLine);
		scan.skip(".*:");
		LinkedList<String> elements = new LinkedList<String>();
		while (scan.hasNext()) {
			elements.add(scan.next());
		}
		scan .close();
		org.prop4j.Node propNode = buildPropNode(elements);
		featureModel.addPropositionalNode(propNode);
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
    		if ((element.equals("~")) && (list.getFirst().equals("(")) 
    									&& (list.getLast().equals(")"))) {
    			list.removeFirst();
				list.removeLast();
				return new Not(buildPropNode(list));
    		}
    		if (element.equals("AND")) element = "and";
    		if (element.equals("OR")) element = "or";
    		if (element.equals("IMP")) element = "imp";
    		if (element.equals("BIIMP")) element = "biimp";
    		if ((element.equals("and")) || (element.equals("or")) || 
    				(element.equals("imp")) || (element.equals("biimp"))) {
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
    				if (element.equals("imp")) 
    					return new Implies(leftResult, rightResult);
    				if (element.equals("biimp")) 
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
			throw new UnsupportedModelException("Fehlendes Element", line);
		element = list.removeFirst();
		if ((element.equals("(")) && (!list.isEmpty())) 
			element = list.removeFirst();
		if (element.equals("~")) {
			return new Not(buildPropNode(list));
		} else {
			Feature feat = idTable.get(element);
			if (feat == null)
				throw new UnsupportedModelException("The feature '" + element + 
						"' does not occur in the grammar!", 0);			
			return new Literal(feat.getName());
		}
    }
    
    private class FeatureIndent extends Feature {
    	
    	private int indentation = 0;
    	
		public FeatureIndent(FeatureModel featureModel) {
			super(featureModel);
		}

		public FeatureIndent(FeatureModel featureModel, int indent) {
			super(featureModel);
			indentation = indent;
		}
		
		public int getIndentation() {
			return indentation;
		}

//		public void setIndentation(int indentation) {
//			this.indentation = indentation;
//		}
    }
    
    private class FeatCardinality {
    	
    	Feature feat;
    	int start;
    	int end;
    	
    	FeatCardinality (Feature feat, int start, int end) {
    		this.feat = feat;
    		this.start = start;
    		this.end = end;
    	}
    	
    }
    
}
