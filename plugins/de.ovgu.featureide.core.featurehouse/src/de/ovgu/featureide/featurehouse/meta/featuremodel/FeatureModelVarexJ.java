/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Collections;
import java.util.List;
import java.util.Locale;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Defines the content of the feature model class specific for VarexJ.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelVarexJ implements IFeatureModelClass {

	private final static String HEAD = "/**\r\n * Variability encoding of the feature model for VarexJ.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n";
	private final static String FIELD_MODIFIER = "\tpublic static boolean ";
	private final static String ANNOTATION = "\t@Conditional\r\n";

	private final FeatureModel featureModel;
	private final ArrayList<Feature> features;

	public FeatureModelVarexJ(FeatureModel featureModel) {
		this.featureModel = featureModel;
		features = new ArrayList<Feature>(featureModel.getFeatures());
		Collections.sort(features, new FeatureComparator(true));
	}
	
	@Override
	public String getImports() {
		return "import gov.nasa.jpf.annotation.Conditional;\r\n\r\n";
	}
		
	@Override
	public String getHead() {
		return HEAD;
	}
 	
	@Override
	public String getFeatureFields() {
		StringBuilder fields = new StringBuilder();
		final List<List<Feature>> deadCoreList = featureModel.getAnalyser().analyzeFeatures();
		for (Feature feature : features) {
			final boolean isCoreFeature = deadCoreList.get(0).contains(feature);
			final boolean isDeadFeature = deadCoreList.get(1).contains(feature);
			if (!isCoreFeature && !isDeadFeature) {
				fields.append(ANNOTATION);
			}
			fields.append(FIELD_MODIFIER);
			fields.append(feature.getName().toLowerCase(Locale.ENGLISH));
			if (isDeadFeature) {
				fields.append(" = false;\r\n");
			} else {
				fields.append(" = true;\r\n");
			}
		}
		return fields.toString();
	}
	
	private final static String TRUE_FALSE = "  &&  True  &&  !False";

	@Override
	public String getFormula() {
		final Node nodes = NodeCreator.createNodes(featureModel.clone()).toCNF();
		String formula = nodes.toString(NodeWriter.javaSymbols);
		if (formula.contains(TRUE_FALSE)) {
			formula = formula.substring(0, formula.indexOf(TRUE_FALSE));
		}
		return VALID + "return " + formula.toLowerCase(Locale.ENGLISH) + ";\r\n\t}\r\n\r\n";
	}

	@Override
	public String getGetter() {
		return "";
	}

	@Override
	public String getSelection() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("\t/**\r\n\t * Select features to run a specific configuration.\r\n\t */\r\n\tpublic static void select(String[] selection) {\r\n\t\t");
		for (int i = 0;i < features.size();i++) {
			if (i != 0) {
				stringBuilder.append("\r\n\t\t");	
			}
			stringBuilder.append(features.get(i).getName().toLowerCase(Locale.ENGLISH));
			stringBuilder.append(" = Boolean.valueOf(selection[");
			stringBuilder.append(i);
			stringBuilder.append("]);");
		}
		stringBuilder.append("\r\n\t}");
		return stringBuilder.toString();
	}

}
