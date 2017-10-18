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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Locale;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.FeatureComparator;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Defines the content of the feature model class specific for VarexJ.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelVarexJ implements IFeatureModelClass {

	private final static String HEAD =
		"/**\r\n * Variability encoding of the feature model for VarexJ.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n";
	private final static String FIELD_MODIFIER = "\tpublic static boolean ";
	private final static String ANNOTATION = "\t@Conditional\r\n";

	private final IFeatureModel featureModel;
	private final ArrayList<IFeature> features;

	public FeatureModelVarexJ(IFeatureModel featureModel) {
		this.featureModel = featureModel;
		features = new ArrayList<IFeature>(Functional.toList(featureModel.getFeatures()));
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
		final StringBuilder fields = new StringBuilder();
		final List<List<IFeature>> deadCoreList = featureModel.getAnalyser().analyzeFeatures();
		for (final IFeature feature : features) {
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

	@Override
	public String getFormula() {
		final AdvancedNodeCreator nc = new AdvancedNodeCreator(featureModel);
		nc.setCnfType(CNFType.Compact);
		nc.setIncludeBooleanValues(false);
		final Node node = nc.createNodes();
		final String formula = node.toString(NodeWriter.javaSymbols).toLowerCase(Locale.ENGLISH);
		return VALID + "return " + formula + ";\r\n\t}\r\n\r\n";
	}

	@Override
	public String getGetter() {
		return "";
	}

	@Override
	public String getSelection() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder
				.append("\t/**\r\n\t * Select features to run a specific configuration.\r\n\t */\r\n\tpublic static void select(String[] selection) {\r\n\t\t");
		for (int i = 0; i < features.size(); i++) {
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
