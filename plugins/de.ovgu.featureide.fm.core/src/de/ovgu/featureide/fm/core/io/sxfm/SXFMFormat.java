/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.io.sxfm;

import static de.ovgu.featureide.fm.core.localization.StringTable.CANT_DETERMINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONNECTIONTYPE_OF_ROOTFEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.COULDNT;
import static de.ovgu.featureide.fm.core.localization.StringTable.COULDNT_MATCH_WITH;
import static de.ovgu.featureide.fm.core.localization.StringTable.DATA;
import static de.ovgu.featureide.fm.core.localization.StringTable.DETERMINE_GROUP_CARDINALITY;
import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY___;
import static de.ovgu.featureide.fm.core.localization.StringTable.GROUP_CARDINALITY;
import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.META;
import static de.ovgu.featureide.fm.core.localization.StringTable.MISSING_ELEMENT;
import static de.ovgu.featureide.fm.core.localization.StringTable.SECOND_TIME_COMMA__BUT_MAY_ONLY_OCCUR_ONCE;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNKNOWN_XML_TAG;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import java.util.regex.Pattern;

import org.prop4j.And;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.NodeWriter;
import org.prop4j.Not;
import org.prop4j.Or;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.AXMLFormat;

/**
 * Reads / Writes feature models in the SXFM format.
 *
 * @author Sebastian Krieter
 */
public class SXFMFormat extends AXMLFormat<IFeatureModel> implements IFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + SXFMFormat.class.getSimpleName();

	private static final Pattern CONTENT_REGEX = Pattern.compile("\\A\\s*(<[?]xml\\s.*[?]>\\s*)?<feature_model[\\s>]");

	private final static String[] symbols = new String[] { "~", " and ", " or ", "", "", ", ", "", "", "" };

	@Override
	public String getSuffix() {
		return "xml";
	}

	@Override
	public IPersistentFormat<IFeatureModel> getInstance() {
		return new SXFMFormat();
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	protected void writeDocument(Document doc) {
		createXmlDoc(doc);
	}

	/**
	 * Creates the DOM Document Representation from the feature model fmodel by using createXmlDocRec
	 *
	 * @param doc Document where the feature model is put
	 */
	private void createXmlDoc(Document doc) {
		final Element elem = doc.createElement("feature_model");
		elem.setAttribute("name", "FeatureIDE model");
		doc.appendChild(elem);
		final Node featTree = doc.createElement("feature_tree");
		elem.appendChild(featTree);
		featTree.appendChild(doc.createTextNode("\n"));
		createXmlDocRec(doc, featTree, object.getStructure().getRoot().getFeature(), false, "");
		createPropositionalConstraints(doc, elem);
	}

	/**
	 * Creates the DOM Document Representation from the feature model fmodel by recursively building the Nodes
	 *
	 * @param doc Document where the feature model is put
	 * @param nod Current Node in the Document Tree
	 * @param feat Current Feature in the feature model Tree
	 * @param andMode true if the connection between the current feature and its parent is of the type "and", false otherwise
	 * @param indent indentation of the parent feature
	 */
	private void createXmlDocRec(Document doc, Node nod, IFeature feat, boolean andMode, String indent) {
		String newIndent;
		Node textNode;
		LinkedList<IFeature> children;
		boolean nextAndMode = false;
		if (feat == null) {
			return;
		}
		final String fName = feat.getName();
		if (feat.getStructure().isRoot()) {
			textNode = doc.createTextNode(":r " + fName + "(" + fName + ")\n");
			newIndent = "\t";
		} else if (andMode) {
			if (feat.getStructure().isMandatory()) {
				textNode = doc.createTextNode(indent + ":m " + fName + "(" + fName + ")\n");
			} else {
				textNode = doc.createTextNode(indent + ":o " + fName + "(" + fName + ")\n");
			}
		} else {
			textNode = doc.createTextNode(indent + ": " + fName + "(" + fName + ")\n");
		}
		nod.appendChild(textNode);
		children = new LinkedList<>(Functional.toList(FeatureUtils.convertToFeatureList(feat.getStructure().getChildren())));
		if (children.isEmpty()) {
			return;
		}
		if (feat.getStructure().isAnd()) {
			nextAndMode = true;
			newIndent = indent + "\t";
		} else if (feat.getStructure().isOr()) {
			textNode = doc.createTextNode(indent + "\t:g [1,*]\n");
			nod.appendChild(textNode);
			newIndent = indent + "\t\t";
			nextAndMode = false;
		} else if (feat.getStructure().isAlternative()) {
			textNode = doc.createTextNode(indent + "\t:g [1,1]\n");
			nod.appendChild(textNode);
			newIndent = indent + "\t\t";
			nextAndMode = false;
		} else {
			throw new IllegalStateException(CANT_DETERMINE + CONNECTIONTYPE_OF_ROOTFEATURE);
		}

		final Iterator<IFeature> i = children.iterator();
		while (i.hasNext()) {
			createXmlDocRec(doc, nod, i.next(), nextAndMode, newIndent);
		}
	}

	/**
	 * Inserts the tags concerning propositional constraints into the DOM document representation
	 *
	 * @param doc
	 * @param FeatMod Parent node for the propositional nodes
	 */
	private void createPropositionalConstraints(Document doc, Node FeatMod) {
		// add a node for constraints in any case
		final Node propConstr = doc.createElement("constraints");
		FeatMod.appendChild(propConstr);
		final Node newNode = doc.createTextNode("\n");
		propConstr.appendChild(newNode);
		if (object.getConstraints().isEmpty()) {
			return;
		}
		// as before
		int i = 1;
		for (final org.prop4j.Node node : FeatureUtils.getPropositionalNodes(object.getConstraints())) {
			// avoid use of parenthesis from the beginning
			// org.prop4j.Node cnf = node.clone().toCNF();

			final org.prop4j.Node cnf = node.toCNF();

			final ArrayList<org.prop4j.Node> literalList = new ArrayList<>();
			if (cnf instanceof And) {
				for (final org.prop4j.Node child : cnf.getChildren()) {
					if (child instanceof Or) {
						literalList.addAll(Arrays.asList(child.getChildren()));
					} else {
						literalList.add(child);
					}
				}
			} else if (cnf instanceof Or) {
				literalList.addAll(Arrays.asList(cnf.getChildren()));
			} else {
				literalList.add(cnf);
			}

			final HashSet<org.prop4j.Node> literalSet = new HashSet<>(literalList.size());
			boolean invalid = false;
			for (final org.prop4j.Node literal : literalList) {
				final Literal negativeliteral = ((Literal) literal).clone();
				negativeliteral.flip();

				if (literalSet.contains(negativeliteral)) {
					invalid = true;
				} else {
					literalSet.add(literal);
				}
			}

			if (!invalid) {
				if (cnf instanceof And) {
					for (final org.prop4j.Node child : cnf.getChildren()) {
						i = createConstraint(doc, propConstr, i, child);
					}
				} else {
					i = createConstraint(doc, propConstr, i, cnf);
				}
			}
		}
	}

	private int createConstraint(Document doc, Node propConstr, int i, org.prop4j.Node node) {
		Node newNode;
		final NodeWriter nw = new NodeWriter(node);
		nw.setSymbols(symbols);
		nw.setEnforceBrackets(true);
		String nodeString = nw.nodeToString();
		// remove the external parenthesis
		if ((nodeString.startsWith("(")) && (nodeString.endsWith(")"))) {
			nodeString = nodeString.substring(1, nodeString.length() - 1);
		}
		// replace the space before a variable
		nodeString = nodeString.replace("~ ", "~");
		newNode = doc.createTextNode("C" + i + ":" + nodeString + "\n");
		propConstr.appendChild(newNode);
		return ++i;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		idTable.clear();
		warnings.clear();
		line = 0;
		object.reset();
		buildFModelRec(doc);
	}

	private int line;

	private final HashMap<String, IFeature> idTable = new HashMap<>();

	/**
	 * Recursively traverses the Document structure
	 *
	 * @param n
	 * @throws UnsupportedModelException
	 */
	private void buildFModelRec(Node n) throws UnsupportedModelException {
		buildFModelStep(n);
		for (Node child = n.getFirstChild(); child != null; child = child.getNextSibling()) {
			buildFModelRec(child);
		}
	}

	/**
	 * Processes a single Xml-Tag.
	 *
	 * @param n
	 * @throws UnsupportedModelException
	 */
	private void buildFModelStep(Node n) throws UnsupportedModelException {
		if (n.getNodeType() != Node.ELEMENT_NODE) {
			return;
		}
		final String tag = n.getNodeName();
		if ("feature_tree".equals(tag)) {
			handleFeatureTree(n);
		} else if ("feature_model".equals(tag)) {
			line++;
			return;
		} else if ("constraints".equals(tag)) {
			line++;
			handleConstraints(n);
		} else if (META.equals(tag)) {
			return;
		} else if (DATA.equals(tag) && META.equals(n.getParentNode().getNodeName())) {
			return;
		} else {
			throw new UnsupportedModelException(UNKNOWN_XML_TAG, line);
		}
	}

	/**
	 * Reads the input in the feature tree section, interprets the input line by line by using buildFeatureTree
	 *
	 * @param n
	 * @throws UnsupportedModelException
	 */
	private void handleFeatureTree(Node n) throws UnsupportedModelException {
		final NodeList children = n.getChildNodes();
		final StringBuilder buffer = new StringBuilder();
		Node node;
		for (int i = 0; i < children.getLength(); i++) {
			node = children.item(i);
			if (node.getNodeType() == Node.TEXT_NODE) {
				buffer.append(node.getNodeValue());
			}
		}
		final BufferedReader reader = new BufferedReader(new StringReader(buffer.toString()));
		buildFeatureTree(reader);
		removeUnnecessaryAbstractFeatures(object.getStructure().getRoot().getFeature());
	}

	private String removeWhitespaces(String str) {
		str = str.trim();
		if (str.contains(" ")) {
			final String temp = str.substring(0, str.indexOf(' ') + 1);
			str = str.substring(str.indexOf(' ') + 1);
			while (str.contains(" ")) {
				str = str.substring(0, str.indexOf(' ')) + str.substring(str.indexOf(' ') + 1, str.length());
			}
			str = temp + str;
		}
		return str;
	}

	/**
	 * Reads one line of the input Text and builds the corresponding feature
	 *
	 * @param reader
	 * @param lastFeat
	 * @throws UnsupportedModelException
	 */
	private void buildFeatureTree(BufferedReader reader) throws UnsupportedModelException {
		try {
			final IFeatureModelFactory factory = FMFactoryManager.getFactory(object);
			FeatureIndent lastFeat = new FeatureIndent(null, -1, null);
			// List of Features with arbitrary cardinalities
			final LinkedList<FeatCardinality> arbCardGroupFeats = new LinkedList<FeatCardinality>();
			String lineText = reader.readLine();
			line++;
			FeatureIndent feat;
			String featId = "";
			while ((lineText = reader.readLine()) != null) {
				int countIndent = 0;

				if (lineText.trim().isEmpty()) {
					line++;
					continue;
				}
				while (lineText.startsWith("\t")) {
					countIndent++;
					lineText = lineText.substring(1);
				}
				int relativeIndent = countIndent - lastFeat.getIndentation();
				while (relativeIndent < 1) {
					// if (lastFeat.isRoot()) throw new UnsupportedModelException(
					// INDENTATION_ERROR_COMMA__FEATURE_HAS_NO_PARENT, line);
					// lastFeat = (FeatureIndent) lastFeat.getParent();
					// relativeIndent = countIndent - lastFeat.getIndentation();

					if (lastFeat != null) {
						lastFeat = lastFeat.getParent();
						relativeIndent = countIndent - lastFeat.getIndentation();
					}
				}
				// Remove special characters and whitespaces from names
				lineText = removeWhitespaces(lineText);

				final char[] lineTextChars = lineText.toCharArray();
				for (int i = 0; i < lineTextChars.length; i++) {
					final Character c = lineTextChars[i];

					if (!(Character.isLetterOrDigit(c) || c.equals(':') || c.equals('[') || c.equals(']') || c.equals(',') || c.equals('*') || c.equals('(')
						|| c.equals(')'))) {
						lineTextChars[i] = '_';
					}
				}

				lineText = new String(lineTextChars);

				if (lineText.startsWith(":r")) {
					feat = new FeatureIndent(null, 0, factory.createFeature(object, ""));
					feat.getFeature().getStructure().setMandatory(true);
					featId = setNameGetID(feat.getFeature(), lineText);
					// if (feat.getName().trim().toLowerCase().equals("root"))
					// feat.setName("root_");
					object.getStructure().setRoot(feat.getFeature().getStructure());
					feat.getFeature().getStructure().setAnd();
					countIndent = 0;
				} else if (lineText.startsWith(":m")) {
					feat = new FeatureIndent(lastFeat, countIndent, factory.createFeature(object, ""));
					feat.getFeature().getStructure().setMandatory(true);
					featId = setNameGetID(feat.getFeature(), lineText);
					feat.getFeature().getStructure().setParent(lastFeat.getFeature().getStructure());
					lastFeat.getFeature().getStructure().addChild(feat.getFeature().getStructure());
					feat.getFeature().getStructure().setAnd();
				} else if (lineText.startsWith(":o")) {
					feat = new FeatureIndent(lastFeat, countIndent, factory.createFeature(object, ""));
					feat.getFeature().getStructure().setMandatory(false);
					featId = setNameGetID(feat.getFeature(), lineText);
					feat.getFeature().getStructure().setParent(lastFeat.getFeature().getStructure());
					lastFeat.getFeature().getStructure().addChild(feat.getFeature().getStructure());
					feat.getFeature().getStructure().setAnd();
				} else if (lineText.startsWith(":g")) {
					// create an abstract feature for each group (could be optimized, but avoid mixing up several groups)
					feat = new FeatureIndent(lastFeat, countIndent, factory.createFeature(object, ""));
					feat.getFeature().getStructure().setMandatory(true);
					feat.getFeature().getStructure().setAbstract(true);
					// try to generate a name that hopefully does not exist in the model
					featId = lastFeat.getFeature().getName() + EMPTY___ + (lastFeat.getFeature().getStructure().getChildrenCount() + 1);
					feat.getFeature().setName(featId);
					feat.getFeature().getStructure().setParent(lastFeat.getFeature().getStructure());
					lastFeat.getFeature().getStructure().addChild(feat.getFeature().getStructure());
					lastFeat = feat;
					if (lineText.contains("[1,1]")) {
						lastFeat.getFeature().getStructure().setAlternative();
					} else if (lineText.contains("[1,*]")) {
						lastFeat.getFeature().getStructure().setOr();
					} else if ((lineText.contains("[")) && (lineText.contains("]"))) {
						final int index = lineText.indexOf('[');
						final int start = Character.getNumericValue(lineText.charAt(index + 1));
						final int end = Character.getNumericValue(lineText.charAt(index + 3));
						final FeatCardinality featCard = new FeatCardinality(lastFeat.getFeature(), start, end);
						arbCardGroupFeats.add(featCard);
					} else {
						throw new UnsupportedModelException(COULDNT + DETERMINE_GROUP_CARDINALITY, line);
					}
					// lastFeat = feat;
					// featId = featId + "_ ";
					line++;
					addFeatureToModel(feat.getFeature());
					continue;
				} else if (lineText.startsWith(":")) {
					feat = new FeatureIndent(lastFeat, countIndent, factory.createFeature(object, ""));
					feat.getFeature().getStructure().setMandatory(true);
					String name;
					if (lineText.contains("(")) {
						name = lineText.substring(2, lineText.indexOf('('));
						featId = lineText.substring(lineText.indexOf('(') + 1, lineText.indexOf(')'));
					} else {
						name = lineText.substring(2, lineText.length()); // + line;
						featId = name;
					}
					if (Character.isDigit(name.charAt(0))) {
						name = "a" + name;
					}
					feat.getFeature().setName(name);
					feat.getFeature().getStructure().setParent(lastFeat.getFeature().getStructure());
					lastFeat.getFeature().getStructure().addChild(feat.getFeature().getStructure());
					feat.getFeature().getStructure().setAnd();
				} else {
					throw new UnsupportedModelException(COULDNT_MATCH_WITH + "known Types: :r, :m, :o, :g, :", line);
				}
				addFeatureToModel(feat.getFeature());

				if (idTable.containsKey(featId)) {
					throw new UnsupportedModelException("Feature \"" + featId + "\" occured" + SECOND_TIME_COMMA__BUT_MAY_ONLY_OCCUR_ONCE, line);
				}
				idTable.put(featId, feat.getFeature());

				lastFeat = feat;
				line++;
			}
			// Check that there are only OR connections when the parent has more than one feature
			for (final IFeature f : object.getFeatures()) {
				if (f.getStructure().isOr() && (f.getStructure().getChildrenCount() <= 1)) {
					f.getStructure().setAnd();
				}
			}

			handleArbitrayCardinality(arbCardGroupFeats);
		} catch (final IOException e) {
			Logger.logError(e);
		}
	}

	private void removeUnnecessaryAbstractFeatures(IFeature feature) {
		if (feature.getStructure().getChildrenCount() == 1) {
			final IFeatureStructure child = feature.getStructure().getFirstChild();
			if (child.isAbstract()) {
				for (final IFeatureStructure grantChild : feature.getStructure().getFirstChild().getChildren()) {
					grantChild.setParent(feature.getStructure());
					feature.getStructure().addChild(grantChild);
				}
				if (child.isAnd()) {
					feature.getStructure().setAnd();
				} else if (child.isOr()) {
					feature.getStructure().setOr();
				} else if (child.isAlternative()) {
					feature.getStructure().setAlternative();
				}
				child.setParent(null);
				feature.getStructure().removeChild(child);
				object.deleteFeatureFromTable(child.getFeature());
			}
		}
		for (final IFeatureStructure child : feature.getStructure().getChildren()) {
			removeUnnecessaryAbstractFeatures(child.getFeature());
		}
	}

	/**
	 * adds Feature feat to the model if the feature name is already taken, a unique identifier i is added to the name (FeatureA -> FeatureA_i)
	 *
	 * @param feat
	 */
	private void addFeatureToModel(IFeature feat) {
		final String orig_name = feat.getName();
		int i = 1;
		while (!object.addFeature(feat)) {
			feat.setName(orig_name + EMPTY___ + i++);
		}

	}

	private String setNameGetID(IFeature feat, String lineText) {
		String featId, name;
		if (lineText.contains("(")) {
			name = lineText.substring(3, lineText.indexOf('('));
			featId = lineText.substring(lineText.indexOf('(') + 1, lineText.indexOf(')'));
		} else {
			name = lineText.substring(3, lineText.length()); // + line;
			featId = name;
		}
		if (Character.isDigit(name.charAt(0))) {
			name = "a" + name;
		}
		feat.setName(name);
		return featId;
	}

	/**
	 * If there are groups with a cardinality other then [1,*] or [1,1], this function makes the necessary adjustments to the model
	 *
	 * @param featList List of features with arbitrary cardinalities
	 * @throws UnsupportedModelException
	 */
	private void handleArbitrayCardinality(LinkedList<FeatCardinality> featList) throws UnsupportedModelException {
		org.prop4j.Node node;
		for (final FeatCardinality featCard : featList) {
			final IFeature feat = featCard.feat;
			final List<IFeatureStructure> children = feat.getStructure().getChildren();
			for (final IFeatureStructure child : children) {
				child.setMandatory(false);
			}
			final int start = featCard.start;
			final int end = featCard.end;
			if ((start < 0) || (start > end) || (end > children.size())) {
				throw new UnsupportedModelException(GROUP_CARDINALITY + INVALID, line);
			}
			final int f = children.size();
			node = buildMinConstr(FeatureUtils.convertToFeatureList(children), (f - start) + 1, feat.getName());
			object.addConstraint(new Constraint(object, node));
			if ((start > 0) && (end < f)) {
				node = buildMaxConstr(FeatureUtils.convertToFeatureList(children), end + 1);
				object.addConstraint(new Constraint(object, node));
			}
		}
	}

	/**
	 * Builds the propositional constraint, denoting a minimum of features has to be selected
	 *
	 * @param list
	 * @param length
	 * @param parentName
	 * @return
	 */
	private org.prop4j.Node buildMinConstr(List<IFeature> list, int length, String parentName) {
		final LinkedList<org.prop4j.Node> result = new LinkedList<org.prop4j.Node>();
		final LinkedList<org.prop4j.Node> partResult = new LinkedList<org.prop4j.Node>();
		final int listLength = list.size();
		final int[] indexes = new int[length];
		final int[] resIndexes = new int[length];
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
					indexes[j] = indexes[j - 1] + 1;
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
	 * Builds the propositional constraint, denoting a maximum of features can be selected
	 *
	 * @param list
	 * @param length
	 * @return
	 */
	private org.prop4j.Node buildMaxConstr(List<IFeature> list, int length) {
		final LinkedList<org.prop4j.Node> result = new LinkedList<org.prop4j.Node>();
		final LinkedList<org.prop4j.Node> partResult = new LinkedList<org.prop4j.Node>();
		final int listLength = list.size();
		final int[] indexes = new int[length];
		final int[] resIndexes = new int[length];
		for (int i = 0; i < length; i++) {
			indexes[i] = i;
			resIndexes[i] = i + (listLength - length);
		}
		while (!Arrays.equals(indexes, resIndexes)) {
			for (int i = 0; i < length; i++) {
				partResult.add(new Literal(list.get(indexes[i]).getName(), false));
			}
			result.add(new Or(partResult));
			for (int i = length - 1; i >= 0; i--) {
				if (indexes[i] >= resIndexes[i]) {
					continue;
				}
				indexes[i] = indexes[i] + 1;
				for (int j = i + 1; j < length; j++) {
					indexes[j] = indexes[j - 1] + 1;
				}
				break;
			}
		}
		for (int i = 0; i < length; i++) {
			partResult.add(new Literal(list.get(indexes[i]).getName(), false));
		}
		result.add(new Or(partResult));
		return new And(result);
	}

	/**
	 * Handles the constraints found in the 'constraints' xml-tag
	 *
	 * @param n
	 * @throws UnsupportedModelException
	 */
	private void handleConstraints(Node n) throws UnsupportedModelException {
		final NodeList children = n.getChildNodes();
		final StringBuilder buffer = new StringBuilder();
		String lineText;
		Node node;
		for (int i = 0; i < children.getLength(); i++) {
			node = children.item(i);
			if (node.getNodeType() == Node.TEXT_NODE) {
				buffer.append(node.getNodeValue());
			}
		}
		final BufferedReader reader = new BufferedReader(new StringReader(buffer.toString()));
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
		} catch (final IOException e) {
			Logger.logError(e);
		}
	}

	/**
	 * Handles a single constraints.
	 *
	 * @param lineText Text description of a Constraint
	 * @throws UnsupportedModelException
	 */
	private void handleSingleConstraint(String lineText) throws UnsupportedModelException {
		String newLine = lineText.replace("(", " ( ");
		newLine = newLine.replace(")", " ) ");
		newLine = newLine.replace("~", " ~ ");
		final Scanner scan = new Scanner(newLine);
		scan.skip(".*:");
		final LinkedList<String> elements = new LinkedList<String>();
		while (scan.hasNext()) {
			elements.add(scan.next());
		}
		scan.close();
		final org.prop4j.Node propNode = buildPropNode(elements);
		object.addConstraint(new Constraint(object, propNode));
	}

	/**
	 * Builds a Propositional Node from a propositional formula
	 *
	 * @param list
	 * @return
	 * @throws UnsupportedModelException
	 */
	private org.prop4j.Node buildPropNode(LinkedList<String> list) throws UnsupportedModelException {
		final LinkedList<String> left = new LinkedList<String>();
		org.prop4j.Node leftResult, rightResult;
		int bracketCount = 0;
		String element;
		while (!list.isEmpty()) {
			element = list.removeFirst();
			if (element.equals("(")) {
				bracketCount++;
			}
			if (element.equals(")")) {
				bracketCount--;
			}
			if ((element.equals("~")) && (list.getFirst().equals("(")) && (list.getLast().equals(")"))) {
				list.removeFirst();
				list.removeLast();
				return new Not(buildPropNode(list));
			}
			if (element.equals("AND")) {
				element = "and";
			}
			if (element.equals("OR")) {
				element = "or";
			}
			if (element.equals("IMP")) {
				element = "imp";
			}
			if (element.equals("BIIMP")) {
				element = "biimp";
			}
			if ((element.equals("and")) || (element.equals("or")) || (element.equals("imp")) || (element.equals("biimp"))) {
				if (bracketCount == 0) {
					if ((left.getFirst().equals("(")) && (left.getLast().equals(")"))) {
						left.removeFirst();
						left.removeLast();
					}
					leftResult = buildPropNode(left);
					if ((list.getFirst().equals("(")) && (list.getLast().equals(")"))) {
						list.removeFirst();
						list.removeLast();
					}
					rightResult = buildPropNode(list);
					if (element.equals("and")) {
						return new And(leftResult, rightResult);
					}
					if (element.equals("or")) {
						return new Or(leftResult, rightResult);
					}
					if (element.equals("imp")) {
						return new Implies(leftResult, rightResult);
					}
					if (element.equals("biimp")) {
						return new Equals(leftResult, rightResult);
					}
				}
			}
			left.add(element);
		}
		return buildLeafNodes(left);
	}

	private org.prop4j.Node buildLeafNodes(LinkedList<String> list) throws UnsupportedModelException {
		String element;
		if (list.isEmpty()) {
			throw new UnsupportedModelException(MISSING_ELEMENT, line);
		}
		element = list.removeFirst();
		if (("(".equals(element)) && (!list.isEmpty())) {
			element = list.removeFirst();
		}
		if ("~".equals(element)) {
			return new Not(buildPropNode(list));
		} else {
			final IFeature feat = idTable.get(element);
			if (feat == null) {
				throw new UnsupportedModelException(THE_FEATURE_ + element + "' does not occur in the grammar!", 0);
			}
			return new Literal(feat.getName());
		}
	}

	private static class FeatureIndent {

		private final FeatureIndent parent;
		private final IFeature feature;
		private final int indentation;

		private FeatureIndent(FeatureIndent parent, int indentation, IFeature feature) {
			this.parent = parent;
			this.indentation = indentation;
			this.feature = feature;
		}

		private int getIndentation() {
			return indentation;
		}

		public FeatureIndent getParent() {
			return parent;
		}

		public IFeature getFeature() {
			return feature;
		}

	}

	private static class FeatCardinality {

		IFeature feat;
		int start;
		int end;

		FeatCardinality(IFeature feat, int start, int end) {
			this.feat = feat;
			this.start = start;
			this.end = end;
		}

	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return supportsRead() && CONTENT_REGEX.matcher(content).find();
	}

	@Override
	public String getName() {
		return "SXFM";
	}

}
