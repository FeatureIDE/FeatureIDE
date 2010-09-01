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
package de.ovgu.featureide.fm.core.io.xml;

import java.io.InputStream;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Stack;

import javax.swing.JOptionPane;
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
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.*;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
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

	Fallback fallback = new Fallback();
	/**
	 * Set this true to see some information about the parseprocess while
	 * developing!
	 */
	Boolean DEBUG_XML = true;

	/**
	 * A kind of mind for the hirachy of the xml model
	 */
	Stack<String[]> parentStack = new Stack<String[]>();

	/**
	 * A kind of mind for the hirachy of the xml contraint model
	 */
	LinkedList<LinkedList<Node>> ruleTemp = new LinkedList<LinkedList<Node>>();

	/**
	 * If occoured an error while reading, set to false and use for fallback
	 */
	boolean isValidWhileReading = true;

	/**
	 * This is a copy ofthe featureModel before import
	 */
	FeatureModel backup = null;

	/**
	 * BufferModel for the parser
	 */
	FeatureModel newFeatureModel = null;

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader#parseInputStream
	 * (java.io.InputStream)
	 */
	@Override
	protected void parseInputStream(InputStream inputStream)
			throws UnsupportedModelException {
		newFeatureModel = new FeatureModel();

		try {

			XMLInputFactory inputFactory = XMLInputFactory.newInstance();
			XMLEventReader eventReader = inputFactory
					.createXMLEventReader(inputStream);

			boolean isInStruct = false;
			boolean isInConstraints = false;
			ruleTemp.add(new LinkedList<Node>());

			while (eventReader.hasNext()) {
				XMLEvent event = eventReader.nextEvent();

				if (event.isStartElement()) {
					StartElement currentStartTag = event.asStartElement();
					String currentTag = currentStartTag.getName()
							.getLocalPart();

					if (isInStruct) {
						// BEGIN XML-reader is reading information about the
						// features
						Boolean isMandatory = false;
						Boolean isAbstract = false;
						String attrName = "noname";
						String parent = parentStack.peek()[1];

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
							if (curName == "mandatory") {
								if (curValue.equals("true")) {
									isMandatory = true;
								} else {
									isMandatory = false;
								}
							}
							if (curName == "abstract") {
								if (curValue.equals("true")) {
									isAbstract = true;
								} else {
									isAbstract = false;
								}
							}
						}
						// END read attributes from XML tag

						//if (!featureNames.contains(attrName)
						//		&& attrName != "noname") {
						if(!newFeatureModel.getFeatureNames().contains(attrName) && FeatureModel.isValidJavaIdentifier(attrName)) {
							addFeature(attrName, isMandatory, isAbstract,
									parent);
						} else {
							isValidWhileReading = false;
							if(!FeatureModel.isValidJavaIdentifier(attrName)) {
								fallback.addError("'" + attrName + "' is not a valid feature name", event.getLocation().getLineNumber());
							}
							if (newFeatureModel.getFeatureNames().contains(attrName)) {
								fallback.addError("Cannot redefine '" + attrName + "'", event.getLocation().getLineNumber());								
							}	
						}

						if (currentTag != "feature") {
							parentStack.push(new String[] { currentTag,
									attrName });
						}
						// END XML-reader is reading information about the
						// features
					} else if (isInConstraints) {
						if (currentTag.equals("rule")
								|| currentTag.equals("constraints")) {
						} else if (currentTag.equals("var")) {
							String literalName = eventReader.getElementText();

							if (newFeatureModel.getFeatureNames().contains(literalName)) {
								ruleTemp.getLast()
										.add(new Literal(literalName));
							} else {
								isValidWhileReading = false;
								fallback.addError("Feature '" + literalName
										+ "' does not exists ", event
										.getLocation().getLineNumber());
							}
						} else {
							ruleTemp.add(new LinkedList<Node>());
						}

					} else {
						if (currentTag.equals("featureModel")) {
						}
						if (currentTag.equals("struct")) {
							parentStack
									.push(new String[] { currentTag, "root" });
							isInStruct = true;
							isInConstraints = false;
						}
						if (currentTag.equals("constraints")) {
							isInStruct = false;
							isInConstraints = true;
						}
					}
				}
				if (event.isEndElement()) {
					EndElement endElement = event.asEndElement();

					String currentTag = endElement.getName().getLocalPart();
					if (isInStruct) {
						if (currentTag != "feature") {
							if (parentStack.peek()[0] == currentTag) {
								parentStack.pop();
							}
						}
						if (currentTag == "struct") {
							isInStruct = false;
							isInConstraints = false;
						}
					} else if (isInConstraints) {
						if (currentTag.equals("rule")) {
							Node node = ruleTemp.getFirst().getFirst();
							boolean addIt = true;
							try {
								if (!new SatSolver(node.clone(), 250)
										.isSatisfiable()) {
									// JOptionPane.showMessageDialog(null,
									// "Constraint will not be added - not satisfiable: \n"+
									// node.toString(), "Warning",
									// JOptionPane.WARNING_MESSAGE );
									// TODO other form of warning
									addIt = false;
								}
								if (!new SatSolver(new Not(node.clone()), 250)
										.isSatisfiable()) {
									// JOptionPane.showMessageDialog(null,
									// "Constraint will not be added - tautology: \n"+
									// node.toString(), "Warning",
									// JOptionPane.WARNING_MESSAGE );
									// TODO other form of warning
									addIt = false;
								}
							} catch (Exception e) {
							}

							if (addIt)
								newFeatureModel.addPropositionalNode(node);
							ruleTemp.clear();
							ruleTemp.add(new LinkedList<Node>());
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
				}
			}
			eventReader.close();
			appendFeatureModel();
		} catch (XMLStreamException e) {
			fallback.addError("Abort parsing - XML is not well formed!", e
					.getLocation().getLineNumber());
		}
		// Update the FeatureModel in Editor

		featureModel.handleModelDataChanged();
		fallback.showErrorLog();
	}

	private void appendFeatureModel() {
		if (isValidWhileReading == true) {
			// TODO apply featureModel data to the given FeatureModel
			//JOptionPane.showMessageDialog(null,
			//		"No Error occoured, now we would apply the Model...", "Well done!",
			//		JOptionPane.WARNING_MESSAGE);
			featureModel.replaceModel(newFeatureModel);
		}
	}
	
	class Fallback {
		LinkedList<String[]> errors = new LinkedList<String[]>();

		public void addError(String message, Integer line) {
			errors.add(new String[] { "" + line, message });
		}

		public boolean hasErrors() {
			if (errors.size() > 0) {
				return true;
			} else {
				return false;
			}
		}

		public void showErrorLog() {
			if (this.hasErrors()) {
				String errormsg = "";
				System.out.println(errors.size());
				for (int i = 0; i < errors.size(); i++) {
					String line = errors.get(i)[0];
					String message = errors.get(i)[1];
					// errormsg.concat("Line " + line + ": " + message + "\n" );
					errormsg = errormsg + "Line " + line + ": " + message
							+ "\n";
				}
				JOptionPane.showMessageDialog(null,
						"The imported Model will not be apllied to the editor.:\n"
								+ errormsg, "Parsing Error",
						JOptionPane.WARNING_MESSAGE);
			}
		}
	}

	/**
	 * Create a new feature and add it to the featureModel.
	 * 
	 * @param featureName
	 *            Srting with the name of the featue
	 * @param isMandatory
	 *            boolean, true it the feature is mandatory
	 * @param isAbstract
	 *            boolean, true if the feature is abstract
	 * @param parent
	 *            String with the name of the parent feature
	 */
	private void addFeature(String featureName, boolean isMandatory,
			boolean isAbstract, String parent) {
		/*
		 * HOWTO: add a child to the FeaturModel
		 * 
		 * first: create an Feature second: set flags like mandatory and
		 * abstract third: add the Feature to the FeatureModel last: get the
		 * parent of the current Feature and add the current Feature as a child
		 * of this parent (Feature)
		 * 
		 * Note: addChild DOESN'T ADD THE FEATURE!
		 */
		Feature feat = null;
		if (parent.equals("root")) {
			feat = newFeatureModel.getFeature(featureName);
			feat.setMandatory(true);
		} else {
			feat = new Feature(newFeatureModel, featureName);
			feat.setMandatory(isMandatory);
			feat.setAbstract(isAbstract);
			newFeatureModel.addFeature(feat);
			newFeatureModel.getFeature(parent).addChild(feat);
		}
	}
}
