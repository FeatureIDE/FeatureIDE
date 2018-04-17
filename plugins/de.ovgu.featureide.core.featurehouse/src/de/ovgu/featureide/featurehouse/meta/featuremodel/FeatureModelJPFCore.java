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
package de.ovgu.featureide.featurehouse.meta.featuremodel;

import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY___;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;

import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Defines the content of the feature model class specific for JPF-Core.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelJPFCore implements IFeatureModelClass {

	private static final String NEWLINE = System.getProperty("line.separator", "\n");

	private final static String HEAD = "/**" + NEWLINE + " * Variability encoding of the feature model for JPF." + NEWLINE + " * Auto-generated class."
		+ NEWLINE + " */" + NEWLINE + "public class FeatureModel {" + NEWLINE + NEWLINE;

	private final static String FIELD_MODIFIER = "\tpublic static Boolean ";
	private StringBuilder stringBuilder;
	private Collection<IFeature> deadFeatures = Collections.emptyList();
	private Collection<IFeature> coreFeatures = Collections.emptyList();
	private final IFeatureModel featureModel;

	public FeatureModelJPFCore(IFeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	@Override
	public String getImports() {
		return IMPORT_JPF;
	}

	@Override
	public String getHead() {
		return HEAD;
	}

	@Override
	public String getFeatureFields() {
		final StringBuffer fields = new StringBuffer();
		for (final String f : FeatureUtils.extractConcreteFeaturesAsStringList(featureModel)) {
			fields.append(FIELD_MODIFIER);
			fields.append(f.toLowerCase(Locale.ENGLISH));
			fields.append("_;" + NEWLINE);
		}

		final ArrayList<IFeature> features = new ArrayList<IFeature>(Functional.toList(featureModel.getFeatures()));
		final List<List<IFeature>> deadCoreList = featureModel.getAnalyser().analyzeFeatures();
		coreFeatures = deadCoreList.get(0);
		deadFeatures = deadCoreList.get(1);
		fields.append(NEWLINE + "\t/**" + NEWLINE + "\t * Core features are set 'selected' and dead features 'unselected'." + NEWLINE
			+ "\t * All other features have unknown selection states." + NEWLINE + "\t */" + NEWLINE + "\tstatic {" + NEWLINE);
		for (final IFeature f : features) {
			if (deadFeatures.contains(f)) {
				fields.append("\t\t" + f.toString().toLowerCase(Locale.ENGLISH));
				fields.append("_ = false;" + NEWLINE);
			}
			if (coreFeatures.contains(f)) {
				fields.append("\t\t" + f.toString().toLowerCase(Locale.ENGLISH));
				fields.append("_ = true;" + NEWLINE);
			}
		}
		fields.append("\t}\r\n");
		return fields.toString();
	}

	@Override
	public String getFormula() {
		stringBuilder = new StringBuilder();
		stringBuilder.append(VALID);
		stringBuilder.append("Verify.resetCounter(0);\r\n");
		final IFeature root = featureModel.getStructure().getRoot().getFeature();
		stringBuilder.append("\t\tboolean " + root.toString().toLowerCase(Locale.ENGLISH) + " = true;\r\n");

		addedFeatures.add(root.toString().toLowerCase(Locale.ENGLISH));
		addFeature(root, getFormulaJPF(featureModel));
		stringBuilder.append(
				"\t\tVerify.incrementCounter(0);\r\n\t\treturn true;\r\n\t}\r\n\r\n\tprivate static boolean random() {\r\n\t\treturn Verify.getBoolean(false);\r\n\t}\r\n\r\n");
		return stringBuilder.toString();
	}

	private final LinkedList<String> addedFeatures = new LinkedList<String>();

	private Node getFormulaJPF(IFeatureModel model) {
		final AdvancedNodeCreator c = new AdvancedNodeCreator(model);
		c.setCnfType(CNFType.Compact);
		c.setOptionalRoot(true);
		return c.createNodes();
	}

	/**
	 * @param root
	 */
	private void addFeature(IFeature f, Node formula) {
		if (f.getStructure().isAlternative()) {
			addAlternative(FeatureUtils.convertToFeatureList(f.getStructure().getChildren()), formula);
		}
		if (f.getStructure().isOr()) {
			addOr(FeatureUtils.convertToFeatureList(f.getStructure().getChildren()), formula);
		}
		if (f.getStructure().isAnd()) {
			addAnd(FeatureUtils.convertToFeatureList(f.getStructure().getChildren()), formula);
		}
	}

	/**
	 * @param children
	 */
	private void addAnd(List<IFeature> children, Node formula) {
		for (final IFeature child : children) {
			stringBuilder.append("\t\tboolean " + child.toString().toLowerCase(Locale.ENGLISH) + " = ");
			if (child.getStructure().isMandatory()) {
				stringBuilder.append(getFeature(child) + ";\r\n");
			} else {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
			}
			addedFeatures.add(child.toString().toLowerCase(Locale.ENGLISH));
			stringBuilder.append(setFormula(formula));
		}
		for (final IFeature child : children) {
			addFeature(child, formula);
		}
	}

	/**
	 * @param children
	 */
	private void addOr(List<IFeature> children, Node formula) {
		String set = "false";
		int i = 0;
		for (final IFeature child : children) {
			stringBuilder.append("\t\tboolean " + child.toString().toLowerCase(Locale.ENGLISH) + " = ");
			if (i == (children.size() - 1)) {
				if (set.isEmpty()) {
					stringBuilder.append(getFeature(child) + ";\r\n\t\tVerify.ignoreIf(Verify.getCounter(0) != 0);\r\n");
				} else {
					stringBuilder.append(getFeature(child) + " ? " + set + " ?  random() : true : false;\r\n");
				}
			} else if (i == 0) {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
				set = child.toString().toLowerCase(Locale.ENGLISH);
			} else {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
				set += " ||" + child.toString().toLowerCase(Locale.ENGLISH);
			}
			addedFeatures.add(child.toString().toLowerCase(Locale.ENGLISH));
			stringBuilder.append(setFormula(formula));
			i++;
		}
		for (final IFeature child : children) {
			addFeature(child, formula);
		}
	}

	/**
	 * @param children
	 */
	private void addAlternative(List<IFeature> children, Node formula) {
		String set = "";
		int i = 0;
		for (final IFeature child : children) {
			stringBuilder.append("\t\tboolean " + child.toString().toLowerCase(Locale.ENGLISH) + " = ");
			if (i == (children.size() - 1)) {
				if (set.isEmpty()) {
					stringBuilder.append(getFeature(child) + ";\r\n");
				} else {
					stringBuilder.append(getFeature(child) + " ? !(" + set + ") : false;\r\n");
				}
			} else if (i == 0) {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
				set = child.toString().toLowerCase(Locale.ENGLISH);
			} else {
				stringBuilder.append(getFeature(child) + " ? " + set + "? false : random() : false;\r\n");
				set = child.toString().toLowerCase(Locale.ENGLISH) + " ||" + set;
			}
			addedFeatures.add(child.toString().toLowerCase(Locale.ENGLISH));
			stringBuilder.append(setFormula(formula));
			i++;
		}
		for (final IFeature child : children) {
			addFeature(child, formula);
		}

	}

	private String getFeature(IFeature f) {
		final String featureName = f.toString().toLowerCase(Locale.ENGLISH);
		final String start = featureName + "_ != null ? " + featureName + "_ : ";
		if (deadFeatures.contains(f.getStructure().getParent())) {
			return start + "false";
		}
		if (coreFeatures.contains(f.getStructure().getParent())) {
			return start + "true";
		}
		return start + f.getStructure().getParent().toString().toLowerCase(Locale.ENGLISH);
	}

	/**
	 * @param formula
	 * @return
	 */
	private String setFormula(Node formula) {
		final ArrayList<Node> actualFormula = new ArrayList<Node>();
		final ArrayList<Node> nextFormula = new ArrayList<Node>();
		for (final Node child : formula.getChildren()) {
			boolean allAdded = true;
			for (final Node feature : child.getChildren()) {
				if (!addedFeatures.contains(feature.toString().toLowerCase(Locale.ENGLISH).replaceFirst("-", ""))) {
					allAdded = false;
					break;
				}
			}
			if (allAdded) {
				actualFormula.add(child);
			} else {
				nextFormula.add(child);
			}
		}
		formula.setChildren(nextFormula.toArray());
		if (actualFormula.isEmpty()) {
			return "";
		}
		return "\t\tVerify.ignoreIf(Verify.getCounter(0) != 0 || !("
			+ new And(actualFormula.toArray()).toString(NodeWriter.javaSymbols).toLowerCase(Locale.ENGLISH) + "));\r\n";
	}

	@Override
	public String getGetter() {
		final StringBuilder stringBuilder = new StringBuilder();
		for (final IFeature f : FeatureUtils.extractConcreteFeatures(featureModel)) {
			final String featureName = f.toString().toLowerCase(Locale.ENGLISH);
			stringBuilder.append("\tpublic static boolean " + featureName + "() {\r\n");
			stringBuilder.append("\t\tif (" + featureName + "_ == null) {\r\n");
			stringBuilder.append("\t\t\t" + featureName + "_ = random();\r\n");
			stringBuilder.append("\t\t\tvalid();\r\n");
			stringBuilder.append("\t\t}\r\n");
			stringBuilder.append("\t\treturn " + featureName + "_;\r\n");
			stringBuilder.append("\t}\r\n\r\n");
		}
		return stringBuilder.toString();
	}

	/**
	 * @return The current feature selection for Java Pathfinder.
	 */
	@Override
	public String getSelection() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("\t/**\r\n\t * @return The current feature-selection.\r\n\t */\r\n\tpublic static String getSelection(boolean names) {\r\n\t\t");
		final List<IFeature> features = new ArrayList<IFeature>(Functional.toList(FeatureUtils.extractConcreteFeatures(featureModel)));
		stringBuilder.append("if (names) return ");
		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				stringBuilder.append(" + ");
			}
			final String name = features.get(i).getName();
			final String lowerName = name.toLowerCase(Locale.ENGLISH);
			stringBuilder.append(" (" + lowerName + "_ != null && " + lowerName + "_ ? \"" + name + "\\r\\n\" : \"\") ");
		}
		stringBuilder.append(";\r\n\t\treturn \"\" + ");
		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				stringBuilder.append(" + \"|\" + ");
			}
			stringBuilder.append(features.get(i).getName().toLowerCase(Locale.ENGLISH) + EMPTY___);
		}
		stringBuilder.append(";\r\n\t}\r\n");
		return stringBuilder.toString();
	}

}
