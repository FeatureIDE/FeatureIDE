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
package de.ovgu.featureide.featurehouse.meta;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Or;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;


/**
 * Generates a class representing the variability encoding of the feature model.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelClassGenerator {

	private StringBuilder stringBuilder = new StringBuilder();

	private LinkedList<Feature> deadFeatures;
	private LinkedList<Feature> coreFeatures;
	
	private static final String head_JPF = "import gov.nasa.jpf.jvm.Verify;\r\n\r\n";
	private final static String head_1 = "/**\r\n * Variability encoding of the feature model.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n\t";
	private static final String bottom_1 = ";\r\n\t}\n\n\tprivate static boolean random() {\r\n\t\t return ";
	private static final String bottom_KeY = ";\r\n\t}\r\n}";
	private static final String bottom_JPF = "Verify.getBoolean();\r\n\t}\r\n\r\n\t/**\r\n\t * @return The current feature-selection.\r\n\t */\r\n\tpublic static String getSelection(boolean names) {\r\n\t\t";

	public FeatureModelClassGenerator(FeatureModel model, boolean KeY) {
		printModel(model, KeY);
	}
	
	/**
	 * @return the stringBuilder
	 */
	public StringBuilder getStringBuilder() {
		return stringBuilder;
	}
	
	public FeatureModelClassGenerator(IFeatureProject featureProject) {
		FeatureModel model = featureProject.getFeatureModel();
		printModel(model, IFeatureProject.DEFAULT_META_PRODUCT_GENERATION.equals(featureProject.getMetaProductGeneration()));
		saveToFile(featureProject.getBuildFolder().getFolder(featureProject.getCurrentConfiguration().getName().split("[.]")[0]).getFile("FeatureModel.java"));
	}
	
	@SuppressWarnings("deprecation")
	public void saveToFile(IFile file) {
		InputStream source = new ByteArrayInputStream(stringBuilder.toString()
				.getBytes(Charset.availableCharsets().get("UTF-8")));
		try {
			if (file.exists()) {
					file.setContents(source, false, true, null);
			} else {
				file.create(source, true, null);
			}
			file.setDerived(true);
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	private void printModel(FeatureModel model, boolean KeY) {
		if (!KeY) {
			stringBuilder.append(head_JPF);
		}
		stringBuilder.append(head_1);
		if (KeY) {
			stringBuilder.append("public static boolean ");
		} else {
			stringBuilder.append("public static Boolean ");
		}
		addFeatures(model, KeY);
		if (!KeY) {
			stringBuilder.append("\t\tVerify.incrementCounter(0);\r\n\t\treturn true");
		} else {
			stringBuilder.append(getFormula2(model));
		}
		
		if (KeY) {
			stringBuilder.append(bottom_KeY);
		} else {
			stringBuilder.append(bottom_1);
			stringBuilder.append(bottom_JPF);
			getSelection(model);
			addGetters(model);
			stringBuilder.append("\r\n}");
		}
	}

	/**
	 * @param model
	 */
	private void addGetters(FeatureModel model) {
		ArrayList<Feature> features = new ArrayList<Feature>(model.getConcreteFeatures());
		for (Feature f : features) {
			String getter = "\tpublic static boolean " + f.toString().toLowerCase() + "() {\r\n";
			getter += "\t\tif (" + f.toString().toLowerCase() + "_ == null) {\r\n";
			getter += "\t\t\t" + f.toString().toLowerCase() + "_ = random();\r\n";
			getter += "\t\t\tfm();\r\n";
			getter += "\t\t}\r\n";
			getter += "\t\treturn " + f.toString().toLowerCase() + "_;\r\n";
			getter += "\t}\r\n\r\n";
			stringBuilder.append(getter);
		}
	}


	/**
	 * @param model 
	 * @return The current feature selection for Java Pathfinder.
	 */
	private void getSelection(FeatureModel model) {
		ArrayList<Feature> features = new ArrayList<Feature>(model.getConcreteFeatures());
		
		stringBuilder.append("if (names) return ");
		for (int i = 0;i < features.size();i++) {
			if (i != 0) {
				stringBuilder.append(" + ");	
			}
			String name = features.get(i).getName();
			stringBuilder.append(" (" + name.toLowerCase()+"_ != null && " + name.toLowerCase() + "_ ? \"" + name + "\\r\\n\" : \"\") ");
		}
		stringBuilder.append(";\r\n\t\treturn ");
		for (int i = 0;i < features.size();i++) {
			if (i != 0) {
				stringBuilder.append(" + \"|\" + ");	
			}
			String name = features.get(i).getName();
			stringBuilder.append(name.toLowerCase() + "_");
		}
		stringBuilder.append(";\r\n\t}\r\n");
	}

	/**
	 * @param model
	 * @return
	 */
	private String getFormula2(FeatureModel model) {
		return "\t\treturn " + NodeCreator.createNodes(model.clone()).toCNF().toString(NodeWriter.javaSymbols).toLowerCase();
	}
	
	private Node getFormula(FeatureModel model) {
		return NodeCreator.createNodes(model.clone()).toCNF();
	}

	
	private void addFeatures(FeatureModel model, boolean KeY) {
		ArrayList<Feature> features = new ArrayList<Feature>(model.getFeatures());
		deadFeatures = model.getAnalyser().getDeadFeatures();
		coreFeatures = model.getAnalyser().getCoreFeatures();
		for (int i = 0;i< features.size();i++) {
			stringBuilder.append(features.get(i).toString().toLowerCase());
			if (i != features.size() - 1) {
				if (KeY) {
					stringBuilder.append(", ");
				} else {
					stringBuilder.append("_, ");
				}
			}
		}
		if (!KeY) {
			stringBuilder.append("_");
		}
		if (!KeY) {
			stringBuilder.append(";\n\n\t/**\r\n\t * Core features are set 'selected' and dead features 'unselected'.\r\n\t * All other features have unknown selection states.\r\n\t */\r\n\tstatic {\r\n");
			for (int i = 0;i< features.size();i++) {
				if (deadFeatures.contains(features.get(i))) {
					stringBuilder.append("\t\t" + features.get(i).toString().toLowerCase()+(KeY ? "" : "_"));
					stringBuilder.append(" = false;\n");
				} if (coreFeatures.contains(features.get(i))) {
					stringBuilder.append("\t\t" + features.get(i).toString().toLowerCase()+(KeY ? "" : "_"));
					stringBuilder.append(" = true;\n");
				} else {
					if (KeY) {
						stringBuilder.append("\t\t" + features.get(i).toString().toLowerCase()+(KeY ? "" : "_"));
						stringBuilder.append(" = random();\n");
					} else {
						//stringBuilder.append(" = null;\n");
					}
				}
			}
			stringBuilder.append("\t}\r\n\r\n");
		} else {
			stringBuilder.append(";\r\n");
		}

		stringBuilder.append("\t/**\r\n\t * This formula represents the validity of the current feature selection.\r\n\t */\r\n\tpublic /*@pure@*/ static boolean fm() {\r\n");
		if (!KeY) {
			stringBuilder.append("\t\tVerify.resetCounter(0);\r\n");
			stringBuilder.append("\t\tboolean " + model.getRoot().toString().toLowerCase() + " = true;\r\n");
			
			Node formula = getFormula(model);
			ArrayList<Node> c = new ArrayList<Node>();
			// remove base feature and the (true && !false) statements
			for (Node child : formula.getChildren()) {
				if (child instanceof Or) {
					c.add(child);
				}
			}
			formula.setChildren(c.toArray());
			addedFeatures.add(model.getRoot().toString().toLowerCase());
			addFeature(model.getRoot(), formula);
		}
		
	}
	
	private LinkedList<String> addedFeatures = new LinkedList<String>();
	
	/**
	 * @param root
	 */
	private void addFeature(Feature f, Node formula) {
		if (f.isAlternative()) {
			addAlternative(f.getChildren(), formula);
		} if (f.isOr()) {
			addOr(f.getChildren(), formula);
		} if (f.isAnd()) {
			addAnd(f.getChildren(), formula);
		}
	}

	/**
	 * @param children
	 */
	private void addAnd(LinkedList<Feature> children, Node formula) {
		for (Feature child : children) {
			stringBuilder.append("\t\tboolean " +child.toString().toLowerCase() + " = ");
			if (child.isMandatory()) {
				stringBuilder.append(getFeature(child) + ";\r\n");
			} else {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
			}
			addedFeatures.add(child.toString().toLowerCase());
			stringBuilder.append(setFormula(formula));
		}
		for (Feature child : children) {
			addFeature(child, formula);
		}
	}

	

	/**
	 * @param children
	 */
	private void addOr(LinkedList<Feature> children, Node formula) {
		String set = "false";
		int i = 0;
		for (Feature child : children) {
			stringBuilder.append("\t\tboolean " +child.toString().toLowerCase() + " = ");
			if (i == children.size() - 1) {
				if (set.isEmpty()) {
					stringBuilder.append(getFeature(child) + ";\r\n\t\tVerify.ignoreIf(Verify.getCounter(0) != 0);\r\n");
				} else {
					stringBuilder.append(getFeature(child) + " ? " + set + " ?  random() : true : false;\r\n");
				}
			} else if (i == 0) {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
				set = child.toString().toLowerCase();
			} else {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
				set += " ||" + child.toString().toLowerCase();
			}
			addedFeatures.add(child.toString().toLowerCase());
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
	private void addAlternative(LinkedList<Feature> children, Node formula) {
		String set = "";
		int i = 0;
		for (Feature child : children) {
			stringBuilder.append("\t\tboolean " + child.toString().toLowerCase() + " = ");
			 if (i == children.size() -1) {
				 if (set.isEmpty()) {
					 stringBuilder.append(getFeature(child) + ";\r\n");
				 } else {
					 stringBuilder.append(getFeature(child) + " ? !(" + set + ") : false;\r\n");
				 }
			} else if (i == 0) {
				stringBuilder.append(getFeature(child) + " ? random() : false;\r\n");
				set = child.toString().toLowerCase();
			} else {
				stringBuilder.append(getFeature(child) + " ? " + set + "? false : random() : false;\r\n");
				set = child.toString().toLowerCase() + " ||" + set;
			}
			addedFeatures.add(child.toString().toLowerCase());
			stringBuilder.append(setFormula(formula));
			i++;
		}
		for (Feature child : children) {
			addFeature(child, formula);
		}
		
	}
	
	private String getFeature(Feature f) {
		String start = f.toString().toLowerCase() + "_ != null ? " + f.toString().toLowerCase() + "_ : ";  
		if (deadFeatures.contains(f.getParent())) {
			return start + "false";
		}
		if (coreFeatures.contains(f.getParent())) {
			return start + "true";
		}
		return start + f.getParent().toString().toLowerCase();
	}
	
	/**
	 * @param formula
	 * @return
	 */
	private String setFormula(Node formula) {
		ArrayList<Node> actualFormula = new ArrayList<Node>();
		ArrayList<Node> nextFormula = new ArrayList<Node>();
		for (Node child : formula.getChildren()) {
			boolean allAdded = true;
			for (Node feature : child.getChildren()) {
				if (!addedFeatures.contains(feature.toString().toLowerCase().replaceFirst("-", ""))) {
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
		return "\t\tVerify.ignoreIf(Verify.getCounter(0) != 0 || !(" + new And(actualFormula.toArray()).toString(NodeWriter.javaSymbols).toLowerCase() + "));\r\n";
	}

}
