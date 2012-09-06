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

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Stack;

import javax.xml.stream.XMLEventReader;
import javax.xml.stream.XMLInputFactory;
import javax.xml.stream.XMLStreamException;
import javax.xml.stream.events.Attribute;
import javax.xml.stream.events.EndElement;
import javax.xml.stream.events.StartElement;
import javax.xml.stream.events.XMLEvent;

import org.prop4j.And;
import org.prop4j.AtMost;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.ModelWarning;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Parses a FeatureModel from XML to the Editor
 * 
 * @author Fabian Wielgorz first version
 * @author Maik Lampe & Dariusz Krolikowski optimized XML
 */
public class XmlFeatureModelReader extends AbstractFeatureModelReader {

	public XmlFeatureModelReader(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}
	
	/**
	 * A kind of mind for the hirachy of the xml model
	 */
	private Stack<String[]> parentStack = new Stack<String[]>();

	/**
	 * A kind of mind for the hirachy of the xml contraint model
	 */
	private LinkedList<LinkedList<Node>> ruleTemp = new LinkedList<LinkedList<Node>>();
	
	/**
	 * A list which will be filled with the featureNames in their appropriate order
	 */
	private ArrayList<String> featureOrderList = new ArrayList<String>();

	private static final String[] validTagsStruct = {"and", "or", "alt", "feature", "direct-alt", "direct-or"};

	private static final String[] validTagsConst = {"var", "conj", "disj", "imp", "eq", "not", "atmost1", "rule"};
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader#parseInputStream
	 * (java.io.InputStream)
	 */
	
	protected boolean isInArray(String str, String[] arr){
		for(int i=0; i<arr.length; i++){
			if (arr[i].equals(str))
				return true;
		}
		return false;
	}
	
	/* 
	 * synchronized should prevent the "NullPointer when saving the feature model" 
	 * see ticket: #277 
	 * */
	@Override
	protected synchronized void parseInputStream(InputStream inputStream)
			throws UnsupportedModelException {
		featureOrderList.clear();

		featureModel.reset();

		try {
			XMLInputFactory inputFactory = XMLInputFactory.newInstance();
			XMLEventReader eventReader = inputFactory
					.createXMLEventReader(inputStream);

			// mode: 0 = start; 1 = struct; 2 = constraints; 3 = comments; 4 = featureOrder
			int mode = 0;
			ruleTemp.clear();
			ruleTemp.add(new LinkedList<Node>());
			FMPoint constraintLocation = null;
			featureModel.getLayout().showHiddenFeatures(true);
			featureModel.getLayout().verticalLayout(false);
			
			while (eventReader.hasNext()) {
				XMLEvent event = eventReader.nextEvent();
				if (event.isStartElement()) {
					StartElement currentStartTag = event.asStartElement();
					String currentTag = currentStartTag.getName().getLocalPart();
					
					if (mode == 1) {
						if (!isInArray(currentTag,validTagsStruct)){
							throw new UnsupportedModelException("'"
									+ currentTag + "' is not a valid tag in struct-section.",
									event.getLocation().getLineNumber());	
						}
						// BEGIN XML-reader is reading information about the
						// features
						boolean isMandatory = false;
						boolean isAbstract = false;
						boolean isHidden = false;
						
						FMPoint featureLocation = null;
						String attrName = "noname";
						String parent = parentStack.peek()[1];

						@SuppressWarnings("unchecked")
						Iterator<Attribute> attributes = currentStartTag
								.getAttributes();

						// BEGIN read attributes from XML tag
						while (attributes.hasNext()) {
							Attribute attribute = attributes.next();
							String curName = attribute.getName().getLocalPart();
							String curValue = attribute.getValue();

							if (curName == "name") {
								attrName = curValue;
							}
							else if (curName == "mandatory") {
								if (curValue.equals("true")) {
									isMandatory = true;
								} else {
									isMandatory = false;
								}
							}
							else if (curName == "abstract") {
								if (curValue.equals("true")) {
									isAbstract = true;
								} else {
									isAbstract = false;
								}
							}
							else if (curName == "hidden") {
								if (curValue.equals("true")) 
									isHidden = true;
								 else 
									isHidden = false;
							}
							else if (curName == "coordinates"){
								String subStringX = curValue.substring(0, curValue.indexOf(", "));
								String subStringY = curValue.substring(curValue.indexOf(", ")+2);
								try {
									featureLocation = new FMPoint(Integer.parseInt (subStringX),
											Integer.parseInt (subStringY));
								} catch (Exception e) {
									throw new UnsupportedModelException(e.getMessage()
											+"is no valid Integer Value",
											event.getLocation().getLineNumber());
								}			
								
							}
							else{
								throw new UnsupportedModelException("'"
										+ curName
										+ "' is not a valid attribute.",
										event.getLocation().getLineNumber());
							}
						}
						// END read attributes from XML tag

						if (!featureModel.getFeatureNames().contains(attrName)
								&& featureModel.isValidFeatureName(attrName)) 
						{
							addFeature(attrName, isMandatory, isAbstract, isHidden,	parent, featureLocation);
						} else {
							if (!featureModel.isValidFeatureName(attrName) ) {
								throw new UnsupportedModelException("'"
										+ attrName
										+ "' is not a valid feature name",
										event.getLocation().getLineNumber());
							}
							if (featureModel.getFeatureNames().contains(
									attrName)) {
								throw new UnsupportedModelException(
										"Cannot redefine '" + attrName + "'",
										event.getLocation().getLineNumber());
							}
						}

						if (currentTag != "feature") {
							parentStack.push(new String[] { currentTag,
									attrName });
						// END XML-reader is reading information about the
						// features
						}

					} else if (mode == 2) {
						if (!isInArray(currentTag,validTagsConst)){
							throw new UnsupportedModelException("'"
									+ currentTag + "' is not a valid tag in constraints-section.",
									event.getLocation().getLineNumber());	
						}
						if (currentTag.equals("rule")) {
							
							@SuppressWarnings("unchecked")
							Iterator<Attribute> attributes = currentStartTag
									.getAttributes();
							
							while (attributes.hasNext()) {
								Attribute attribute = attributes.next();
								String curName = attribute.getName().getLocalPart();
								String curValue = attribute.getValue();
								
								if (curName == "coordinates"){
									String subStringX = curValue.substring(0, curValue.indexOf(", "));
									String subStringY = curValue.substring(curValue.indexOf(", ")+2);
									try {
										constraintLocation = new FMPoint(Integer.parseInt (subStringX),
												Integer.parseInt (subStringY));
									} catch (Exception e) {
										throw new UnsupportedModelException(e.getMessage()
												+"is no valid Integer Value",event.getLocation().getLineNumber());
									}					
								} else {
									throw new UnsupportedModelException("'"
											+ curName
											+ "' is not a valid attribute.",
											event.getLocation().getLineNumber());
								}
								
							}
						} else if (currentTag.equals("constraints")){
							
						} else if (currentTag.equals("var")) {
							String literalName = eventReader.getElementText();

							if (featureModel.getFeatureNames().contains(
									literalName)) {
								ruleTemp.getLast()
										.add(new Literal(literalName));
							} else {
								throw new UnsupportedModelException("Feature '"
										+ literalName + "' does not exist.",
										event.getLocation().getLineNumber());
							}
						} else {
							ruleTemp.add(new LinkedList<Node>());
						}

					} 
					else if (mode == 3) {
						if (currentTag.equals("c")){
							featureModel.addComment(eventReader.getElementText()); 
						}
						else{
							throw new UnsupportedModelException("'"
										+ currentTag + "' is not a valid tag in comment-section.",
										event.getLocation().getLineNumber());	
						}
					}else if (mode == 4){
						if (currentTag.equals("feature")){
							@SuppressWarnings("unchecked")
							Iterator<Attribute> attributes = currentStartTag
									.getAttributes();

							// BEGIN read attributes from XML tag
							while (attributes.hasNext()) {
								Attribute attribute = attributes.next();
								String curName = attribute.getName().getLocalPart();
								String curValue = attribute.getValue();
								
								if (currentTag.equals("feature") && curName.equals("name") &&
										featureModel.getFeatureNames().contains(curValue)){
											featureOrderList.add(curValue);
								}
							}
						} else {
							throw new UnsupportedModelException("'"
										+ currentTag + "' is not a valid tag in featureOrder-section.",
										event.getLocation().getLineNumber());	
						}
					}
					else {
						if (currentTag.equals("featureModel")) {
	
							@SuppressWarnings("unchecked")
							Iterator<Attribute> attributes = currentStartTag
									.getAttributes();
							boolean hasAttributes = false;
							while (attributes.hasNext()) {
								hasAttributes = true;
								Attribute attribute = attributes.next();
								String curName = attribute.getName().getLocalPart();
								String curValue = attribute.getValue();
								
								if (curName == "chosenLayoutAlgorithm"){
									try {
										featureModel.getLayout().setLayout(Integer.parseInt(curValue));
									} catch (Exception e) {
										throw new UnsupportedModelException(e.getMessage()
												+"is no valid Integer Value",
												event.getLocation().getLineNumber());
									}			
								} else if (curName == "showHiddenFeatures"){
									if(curValue.equals("false")){
										featureModel.getLayout().showHiddenFeatures(false);
									}
								} else if (curName == "horizontalLayout"){
									if(curValue.equals("true")){
										featureModel.getLayout().verticalLayout(true);
									}			
								}else{
									throw new UnsupportedModelException("'"
											+ curName
											+ "' is not a valid attribute.",
											event.getLocation().getLineNumber());
								}
							}					
							if(!hasAttributes) {
								featureModel.getLayout().setLayout(1);
							}
						}
						else if (currentTag.equals("struct")) {
							parentStack.push(new String[] { currentTag, "root" });	
							
							mode = 1;
						}
						else if (currentTag.equals("constraints")) {
							mode = 2;
						}
						else if (currentTag.equals("comments")) {
							mode = 3;
						}
						else if (currentTag.equals("featureOrder")) {
							featureModel.setFeatureOrderInXML(true);
							
							@SuppressWarnings("unchecked")
							Iterator<Attribute> attributes = currentStartTag
									.getAttributes();
							// BEGIN read attributes from XML tag
							while (attributes.hasNext()) {
								Attribute attribute = attributes.next();
								String curName = attribute.getName().getLocalPart();
								String curValue = attribute.getValue();
								if(currentTag.equals("featureOrder") && curName.equals("userDefined")){
									featureModel.setFeatureOrderUserDefined(Boolean.parseBoolean(curValue));
									break;
								}
							}
							mode = 4;
						}
					}
				}
				if (event.isEndElement()) {
					EndElement endElement = event.asEndElement();

					String currentTag = endElement.getName().getLocalPart();
					if (mode == 1) {
						if (!currentTag.equals("feature")) {
							if (parentStack.peek()[0].equals(currentTag)) {
								parentStack.pop();
							}
						}
						if (currentTag.equals("struct")) {
							mode = 0;
						}
					} else if (mode == 2) {
						if (currentTag.equals("constraints")) {
							mode = 0;
						}
						if (currentTag.equals("rule")) {
							if (!ruleTemp.isEmpty()) {
								if (!ruleTemp.getFirst().isEmpty()) {
									Node node = ruleTemp.getFirst().getFirst();
									try {
										if (! new SatSolver(node.clone(), 250)
												.isSatisfiable()) {
											warnings.add(new ModelWarning("Constraint is unsatisfiable.", event.getLocation().getLineNumber()));
										}
										if (!new SatSolver(
												new Not(node.clone()), 250)
												.isSatisfiable()) {
											warnings.add(new ModelWarning("Constraint is tautology.", event.getLocation().getLineNumber()));
										}
									} catch (Exception e) {
										throw new UnsupportedModelException(e.getMessage(),event.getLocation().getLineNumber());
									}

									featureModel.addPropositionalNode(node);
									featureModel.getConstraints().get(
											featureModel.getConstraintCount()-1).setLocation(constraintLocation);
									constraintLocation = null;
									ruleTemp.clear();
									ruleTemp.add(new LinkedList<Node>());
								}
							}

						} else if (currentTag.equals("conj")) {
							And node = new And();
							node.setChildren(ruleTemp.getLast());
							ruleTemp.removeLast();
							ruleTemp.getLast().addLast(node);
						} else if (currentTag.equals("atmost1")) {
							AtMost node = new AtMost(1);
							node.setChildren(ruleTemp.getLast());
							ruleTemp.removeLast();
							ruleTemp.getLast().addLast(node);
						} else if (currentTag.equals("disj")) {
							Or node = new Or();
							node.setChildren(ruleTemp.getLast());
							ruleTemp.removeLast();
							ruleTemp.getLast().addLast(node);
						} else if (currentTag.equals("imp")) {
							Implies node = new Implies(ruleTemp.getLast()
									.getFirst(), ruleTemp.getLast().getLast());
							ruleTemp.removeLast();
							ruleTemp.getLast().add(node);
						} else if (currentTag.equals("eq")) {
							Equals node = new Equals(ruleTemp.getLast()
									.getFirst(), ruleTemp.getLast().getLast());
							ruleTemp.removeLast();
							ruleTemp.getLast().add(node);
						} else if (currentTag.equals("not")) {
							Not node = new Not(ruleTemp.getLast().getFirst());
							ruleTemp.removeLast();
							ruleTemp.getLast().add(node);
						}
					}
					else if (mode == 3){
						if (currentTag.equals("comments"))
							mode = 0;
					}
					else if (mode == 4){
						if (currentTag.equals("featureOrder")){
							featureModel.setFeatureOrderList(featureOrderList);
							mode = 0;
						}
					}
				}
			}
			eventReader.close();
		} catch (XMLStreamException e) {
			throw new UnsupportedModelException(e.getMessage(), e.getLocation()
					.getLineNumber());
		}
		// Update the FeatureModel in Editor
		featureModel.handleModelDataLoaded();
	}

	/**
	 * Create a new feature and add it to the featureModel.
	 * 
	 * @param featureName
	 *            String with the name of the feature
	 * @param isMandatory
	 *            boolean, true it the feature is mandatory
	 * @param isAbstract
	 *            boolean, true if the feature is abstract
	 * @param parent
	 *            String with the name of the parent feature
	 */
	private void addFeature(String featureName, boolean isMandatory,
			boolean isAbstract, boolean isHidden, String parent, FMPoint location) {
		/*
		 * HOWTO: add a child to the FeaturModel
		 * 
		 * first: create an Feature 
		 * second: set flags like mandatory and
		 * abstract 
		 * third: add the Feature to the FeatureModel 
		 * last: get the parent of the current Feature and add the current Feature as a child
		 * of this parent (Feature)
		 * 
		 * Note: addChild DOESN'T ADD THE FEATURE!
		 */
		Feature feat = null;
		if (parent.equals("root")) {
			feat = featureModel.getFeature(featureName);
			if (feat == null) {
				FMCorePlugin.getDefault().reportBug(277);
			} else {
				feat.setAbstract(isAbstract);
			}
		} else {
			feat = new Feature(featureModel, featureName);
			feat.setMandatory(isMandatory);
			feat.setAbstract(isAbstract);
			feat.setHidden(isHidden);
			
			featureModel.addFeature(feat);
			if (parentStack.peek()[0].equals("and")) {
				featureModel.getFeature(parent).setAnd();
			} else if (parentStack.peek()[0].equals("or")) {
				featureModel.getFeature(parent).setOr();
			} else {
				featureModel.getFeature(parent).setAlternative();
			}
			featureModel.getFeature(parent).addChild(feat);
		}
		if(location != null && feat != null){
			FeatureModel.setFeatureLocation(location, feat);
		}
	}
}