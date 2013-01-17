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
import org.prop4j.NodeWriter;

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
	
	private static final String head_JPF = "import gov.nasa.jpf.jvm.Verify;\r\n\r\n";
	private final static String head_1 = "/**\r\n * Variability encoding of the feature model.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n\t//@ static invariant fm();\n\tpublic ";
	private final static String head_2 = "static boolean "; 
	private static final String bottom_1 = ";\r\n\t}\n\n\tprivate static boolean random() {\r\n\t\t return ";
	private static final String bottom_KeY = "Math.random() > 0.5;\r\n\t}\r\n}";
	private static final String bottom_JPF = "Verify.getBoolean();\r\n\t}\r\n\r\n\t/**\r\n\t * @return The current feature-selection.\r\n\t */\r\n\tpublic static String getSelection() {\r\n\t\t";

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
			stringBuilder.append("final ");
		}
		stringBuilder.append(head_2);
		addFeatures(model, KeY);
		stringBuilder.append(getFormula(model));
		stringBuilder.append(bottom_1);
		if (KeY) {
			stringBuilder.append(bottom_KeY);
		} else {
			stringBuilder.append(bottom_JPF);
			getSelection(model);
			stringBuilder.append(";\r\n\t}\r\n}");
		}
	}

	/**
	 * @param model 
	 * @return The current feature selection for Java Pathfinder.
	 */
	private void getSelection(FeatureModel model) {
		ArrayList<Feature> features = new ArrayList<Feature>(model.getFeatures());
		stringBuilder.append("return ");
		for (int i = 0;i < features.size();i++) {
			if (i != 0) {
				stringBuilder.append(" + \"\\r\\n");	
			} else {
				stringBuilder.append("\"");
			}
			String name = features.get(i).getName();
			stringBuilder.append(name + ": \" + " + name.toLowerCase() + " " );
		}
	}

	/**
	 * @param model
	 * @return
	 */
	private String getFormula(FeatureModel model) {
		String formula = NodeCreator.createNodes(model.clone()).toCNF()
				.toString(NodeWriter.javaSymbols).toLowerCase();
		return formula.substring(0, formula.indexOf("  &&  true  &&  !false"));
	}

	/**
	 * @param features
	 * @param deadFeatures 
	 */
	private void addFeatures(FeatureModel model, boolean KeY) {
		ArrayList<Feature> features = new ArrayList<Feature>(model.getFeatures());
		LinkedList<Feature> deadFeatures = model.getAnalyser().getDeadFeatures();
		LinkedList<Feature> coreFeatures = model.getAnalyser().getCoreFeatures();
		for (int i = 0;i< features.size();i++) {
			stringBuilder.append(features.get(i).toString().toLowerCase());
			if (i != features.size() - 1) {
				stringBuilder.append(" ,");
			}
		}
		stringBuilder.append(";\n\n\t/**\r\n\t * Core features are set 'selected' and dead features 'unselected'.\r\n\t * All other features have unknown selection states.\r\n\t */\r\n\tstatic {\n");
		
		for (int i = 0;i< features.size();i++) {
			stringBuilder.append("\t\t" + features.get(i).toString().toLowerCase());
			if (deadFeatures.contains(features.get(i))) {
				stringBuilder.append(" = false;\n");
			} if (coreFeatures.contains(features.get(i))) {
				stringBuilder.append(" = true;\n");
			} else {
				stringBuilder.append(" = random();\n");
			}
		}
		if (KeY) {
			stringBuilder.append("\t\tif (!fm()) {\n\t\t\tthrow new Error();\r\n\t\t}\r\n");
		}
		stringBuilder.append("\t}\r\n\r\n\t/**\r\n\t * This formula represents the validity of the current feature selection.\r\n\t */\r\n\tpublic /*@pure@*/ static boolean fm() {\n\t\treturn ");
	}

}
