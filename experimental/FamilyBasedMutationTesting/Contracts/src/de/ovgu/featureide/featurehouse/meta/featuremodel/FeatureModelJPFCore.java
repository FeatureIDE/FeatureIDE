/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;

import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Defines the content of the feature model class specific for JPF-Core.
 * 
 * @author Jens Meinicke
 */
class FeatureModelJPFCore implements IFeatureModelClass {

	private static final String HEAD = "/**\r\n * Variability encoding of the feature model for JPF.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n";
	private static final String FIELD_MODIFIER = "\tpublic /*@ nullable @*/ static Boolean ";
	private StringBuilder stringBuilder;
	private Collection<Feature> deadFeatures;
	private Collection<Feature> coreFeatures;
	private FeatureModel featureModel;
	private List<String> addedFeatures = new LinkedList<String>();

	FeatureModelJPFCore(final FeatureModel featureModel) {
		this.featureModel = featureModel;
	}
	
	
	@Override
    public final String getImports() {
		return IMPORT_JPF;
	}

	@Override
    public final String getHead() {
		return HEAD;
	}

	@Override
    public final String getFeatureFields() {
		final StringBuilder fields = new StringBuilder();
		for (final String feature : featureModel.getFeatureNames()) {
			fields.append(FIELD_MODIFIER);
			fields.append(feature.toLowerCase(Locale.ENGLISH));
			fields.append("_ = null;\r\n");
		}

		ArrayList<Feature> features = new ArrayList<Feature>(
				featureModel.getFeatures());
		deadFeatures = featureModel.getAnalyser()
				.getDeadFeatures();
		coreFeatures = featureModel.getAnalyser()
				.getCoreFeatures();
		fields.append("\r\n\t/**\r\n\t * Core features are set 'selected' and dead features 'unselected'.\r\n\t * All other features have unknown selection states.\r\n\t */\r\n\tstatic {\r\n");
		for (final Feature feature : features) {
			if (deadFeatures.contains(feature)) {
			    fields.append("\t\t");
				fields.append(feature.toString().toLowerCase(Locale.ENGLISH));
				fields.append("_ = false;\r\n");
			}
			if (coreFeatures.contains(feature)) {
			    fields.append("\t\t");
				fields.append(feature.toString().toLowerCase(Locale.ENGLISH));
				fields.append("_ = true;\r\n");
			}
		}
		fields.append("\t}\r\n");
		return fields.toString();
	}

	@Override
    public final String getFormula() {
		stringBuilder = new StringBuilder();
		stringBuilder.append(VALID);
		stringBuilder.append("Verify.resetCounter(0);\r\n");
		Feature root = featureModel.getRoot();
		stringBuilder.append("\t\tboolean "
				+ root.toString().toLowerCase(Locale.ENGLISH) + " = true;\r\n");

		Node formula = getFormulaJPF(featureModel);
		ArrayList<Node> c = new ArrayList<Node>();
		// remove base feature and the (true && !false) statements
		for (Node child : formula.getChildren()) {
			if (child instanceof Or) {
				c.add(child);
			}
		}
		formula.setChildren(c.toArray());
		addedFeatures.add(root.toString().toLowerCase(Locale.ENGLISH));
		addFeature(root, formula);
		stringBuilder.append("\t\tVerify.incrementCounter(0);\r\n\t\treturn true;\r\n\t}\r\n\r\n\tprivate static boolean random() {\r\n\t\treturn Verify.getBoolean(false);\r\n\t}\r\n\r\n");
		return stringBuilder.toString();
	}

	private Node getFormulaJPF(final FeatureModel model) {
		return NodeCreator.createNodes(model.clone()).toCNF();
	}
	
	/**
	 * @param root
	 */
	private void addFeature(final Feature f, final Node formula) {
		if (f.isAlternative()) {
			addAlternative(f.getChildren(), formula);
		}
		if (f.isOr()) {
			addOr(f.getChildren(), formula);
		}
		if (f.isAnd()) {
			addAnd(f.getChildren(), formula);
		}
	}

	/**
	 * @param children
	 */
	private void addAnd(final LinkedList<Feature> children, final Node formula) {
		for (Feature child : children) {
			stringBuilder.append("\t\tboolean "
					+ child.toString().toLowerCase(Locale.ENGLISH) + " = ");
			if (child.isMandatory()) {
				stringBuilder.append(getFeature(child) + ";\r\n");
			} else {
				stringBuilder.append(getFeature(child)
						+ " ? random() : false;\r\n");
			}
			addedFeatures.add(child.toString().toLowerCase(Locale.ENGLISH));
			stringBuilder.append(setFormula(formula));
		}
		for (Feature child : children) {
			addFeature(child, formula);
		}
	}

	/**
	 * @param children
	 */
	private void addOr(final LinkedList<Feature> children, final Node formula) {
		String set = "false";
		int i = 0;
		for (Feature child : children) {
			stringBuilder.append("\t\tboolean "
					+ child.toString().toLowerCase(Locale.ENGLISH) + " = ");
			if (i == children.size() - 1) {
				if (set.isEmpty()) {
					stringBuilder
							.append(getFeature(child)
									+ ";\r\n\t\tVerify.ignoreIf(Verify.getCounter(0) != 0);\r\n");
				} else {
					stringBuilder.append(getFeature(child) + " ? " + set
							+ " ?  random() : true : false;\r\n");
				}
			} else if (i == 0) {
				stringBuilder.append(getFeature(child)
						+ " ? random() : false;\r\n");
				set = child.toString().toLowerCase(Locale.ENGLISH);
			} else {
				stringBuilder.append(getFeature(child)
						+ " ? random() : false;\r\n");
				set += " ||" + child.toString().toLowerCase(Locale.ENGLISH);
			}
			addedFeatures.add(child.toString().toLowerCase(Locale.ENGLISH));
			stringBuilder.append(setFormula(formula));
			i++;
		}
		for (Feature child : children) {
			addFeature(child, formula);
		}
	}

	/**
	 * @param children
	 */
	private void addAlternative(final LinkedList<Feature> children, final Node formula) {
		String set = "";
		int i = 0;
		for (Feature child : children) {
			stringBuilder.append("\t\tboolean "
					+ child.toString().toLowerCase(Locale.ENGLISH) + " = ");
			if (i == children.size() - 1) {
				if (set.isEmpty()) {
					stringBuilder.append(getFeature(child) + ";\r\n");
				} else {
					stringBuilder.append(getFeature(child) + " ? !(" + set
							+ ") : false;\r\n");
				}
			} else if (i == 0) {
				stringBuilder.append(getFeature(child)
						+ " ? random() : false;\r\n");
				set = child.toString().toLowerCase(Locale.ENGLISH);
			} else {
				stringBuilder.append(getFeature(child) + " ? " + set
						+ "? false : random() : false;\r\n");
				set = child.toString().toLowerCase(Locale.ENGLISH) + " ||"
						+ set;
			}
			addedFeatures.add(child.toString().toLowerCase(Locale.ENGLISH));
			stringBuilder.append(setFormula(formula));
			i++;
		}
		for (Feature child : children) {
			addFeature(child, formula);
		}

	}

	private String getFeature(final Feature f) {
		String featureName = f.toString().toLowerCase(Locale.ENGLISH);
		String start = featureName + "_ != null ? " + featureName + "_ : ";
		if (deadFeatures.contains(f.getParent())) {
			return start + "false";
		}
		if (coreFeatures.contains(f.getParent())) {
			return start + "true";
		}
		return start + f.getParent().toString().toLowerCase(Locale.ENGLISH);
	}

	/**
	 * @param formula
	 * @return
	 */
	private String setFormula(final Node formula) {
		final ArrayList<Node> actualFormula = new ArrayList<Node>();
		final ArrayList<Node> nextFormula = new ArrayList<Node>();
		for (final Node child : formula.getChildren()) {
			boolean allAdded = true;
			for (final Node feature : child.getChildren()) {
				if (!addedFeatures.contains(feature.toString()
						.toLowerCase(Locale.ENGLISH).replaceFirst("-", ""))) {
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
				+ new And(actualFormula.toArray()).toString(
						NodeWriter.javaSymbols).toLowerCase(Locale.ENGLISH)
				+ "));\r\n";
	}

	@Override
    public final String getGetter() {
		final StringBuilder builder = new StringBuilder();
		final ArrayList<Feature> features = new ArrayList<Feature>(featureModel.getConcreteFeatures());
		for (final Feature feature : features) {
			final String featureName = feature.toString().toLowerCase(Locale.ENGLISH);
			builder.append("\tpublic static boolean " + featureName + "() {\r\n");
			builder.append("\t\tif (" + featureName + "_ == null) {\r\n");
			builder.append("\t\t\t" + featureName + "_ = random();\r\n");
			builder.append("\t\t\tvalid();\r\n");
			builder.append("\t\t}\r\n");
			builder.append("\t\treturn " + featureName + "_;\r\n");
			builder.append("\t}\r\n\r\n");
		}
		return builder.toString();
	}

	/**
	 * @return The current feature selection for Java Pathfinder.
	 */
	public final String getSelection() {
		StringBuilder builder = new StringBuilder();
		builder.append("\t/**\r\n\t * @return The current feature-selection.\r\n\t */\r\n\tpublic static String getSelection(boolean names) {\r\n\t\t");
		ArrayList<Feature> features = new ArrayList<Feature>(featureModel.getConcreteFeatures());
		builder.append("if (names) return ");
		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				builder.append(" + ");	
			}
			String name = features.get(i).getName();
			String lowerName = name.toLowerCase(Locale.ENGLISH);
			builder.append(" (" + lowerName+"_ != null && " + lowerName + "_ ? \"" + name + "\\r\\n\" : \"\") ");
		}
		builder.append(";\r\n\t\treturn \"\" + ");
		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				builder.append(" + \"|\" + ");	
			}
			builder.append(features.get(i).getName().toLowerCase(Locale.ENGLISH) + "_");
		}
		builder.append(";\r\n\t}\r\n");
		return builder.toString();
	}

}
