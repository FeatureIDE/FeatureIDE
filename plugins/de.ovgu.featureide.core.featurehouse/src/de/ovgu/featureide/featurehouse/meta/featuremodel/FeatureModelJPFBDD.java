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
import java.util.Locale;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Defines the content of the feature model class specific for JPF-BDD.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureModelJPFBDD implements IFeatureModelClass {

	private final static String HEAD =
		"/**\r\n * Variability encoding of the feature model for JPF-BDD.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n";
	private final static String FIELD_MODIFIER = "\tpublic static boolean ";
	private final static String ANNOTATION = "\t@gov.nasa.jpf.bdd.TrackWithBDD\r\n";
	private static final String SELECTFEATURES = "\tpublic static void select_features() {\r\n";
	private final IFeatureModel featureModel;

	public FeatureModelJPFBDD(IFeatureModel featureModel) {
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
		final StringBuilder fields = new StringBuilder();
		for (final CharSequence f : Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getFeatures()))) {
			fields.append(ANNOTATION);
			fields.append(FIELD_MODIFIER);
			fields.append(f.toString().toLowerCase(Locale.ENGLISH));
			fields.append(";\r\n");
		}

		fields.append(SELECTFEATURES);

		for (final CharSequence f : Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getFeatures()))) {
			fields.append("\t\t");
			fields.append(f.toString().toLowerCase(Locale.ENGLISH));
			fields.append(" = Verify.getBoolean(false);\r\n");
		}
		fields.append("\t}\r\n");

		return fields.toString();
	}

	@Override
	public String getFormula() {
		final AdvancedNodeCreator nc = new AdvancedNodeCreator(featureModel);
		nc.setCnfType(CNFType.Compact);
		nc.setIncludeBooleanValues(false);
		final Node node = nc.createNodes();
		final String formula = node.toString(NodeWriter.javaSymbols).toLowerCase(Locale.ENGLISH);
		return VALID + "return " + formula + ";\r\n\t}\r\n";
	}

	@Override
	public String getGetter() {
		return "";
	}

	@Override
	public String getSelection() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("\t/**\r\n\t * @return The current feature-selection.\r\n\t */\r\n\tpublic static String getSelection(boolean names) {\r\n\t\t");
		final ArrayList<IFeature> features = new ArrayList<IFeature>(Functional.toList(FeatureUtils.extractConcreteFeatures(featureModel)));
		stringBuilder.append("if (names) return ");
		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				stringBuilder.append(" + ");
			}
			final String name = features.get(i).getName();
			final String lowerName = name.toLowerCase(Locale.ENGLISH);
			stringBuilder.append(" (" + lowerName + " ? \"" + name + "\\r\\n\" : \"\") ");
		}
		stringBuilder.append(";\r\n\t\treturn \"\" + ");
		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				stringBuilder.append(" + \"|\" + ");
			}
			stringBuilder.append(features.get(i).getName().toLowerCase(Locale.ENGLISH));
		}
		stringBuilder.append(";\r\n\t}\r\n");
		return stringBuilder.toString();
	}

}
