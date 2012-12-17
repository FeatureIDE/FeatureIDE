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
	
	private final static String head = "/**\r\n * Variability encoding of the feature model.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n\t//@ static invariant fm();\n\tpublic final static boolean ";
	private static final String bottom = ";\n\t}\n\n\tprivate static boolean random() {\n\t\t return Math.random() > 0.5;\n\t}\n}";

	public FeatureModelClassGenerator(IFeatureProject featureProject) {
		FeatureModel model = featureProject.getFeatureModel();
		printModel(model);
		saveToFile(featureProject.getBuildFolder().getFolder(featureProject.getCurrentConfiguration().getName().split("[.]")[0]).getFile("FeatureModel.java"));
	}
	
	public void saveToFile(IFile file) {
		InputStream source = new ByteArrayInputStream(stringBuilder.toString()
				.getBytes(Charset.availableCharsets().get("UTF-8")));
		try {
			if (file.exists()) {
					file.setContents(source, false, true, null);
			} else {
				file.create(source, true, null);
			}
			file.setDerived(true, null);
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	public FeatureModelClassGenerator(FeatureModel model) {
		printModel(model);
	}

	private void printModel(FeatureModel model) {
		stringBuilder.append(head);
		addFeatures(model);
		stringBuilder.append(getFormula(model));
		stringBuilder.append(bottom);
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
	private void addFeatures(FeatureModel model) {
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
		stringBuilder.append("\t\tif (!fm()) {\n\t\t\tthrow new Error();\n\t\t}\n\t}\n\n\t/**\r\n\t * This formula represents the validity of the current feature selection.\r\n\t */\r\n\tpublic /*@pure@*/ static boolean fm() {\n\t\treturn ");
	}

}
