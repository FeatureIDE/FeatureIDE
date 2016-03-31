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
import java.util.Locale;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Defines the content of the feature model class specific for JPF-BDD.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelJPFBDD implements IFeatureModelClass {
	
	private static final String HEAD = "/**\r\n * Variability encoding of the feature model for JPF-BDD.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n";
	private static final String FIELD_MODIFIER = "\tpublic static boolean ";
	private static final String ANNOTATION = "\t@gov.nasa.jpf.bdd.TrackWithBDD\r\n";
	private static final String SELECTFEATURES = "\tpublic static void select_features() {\r\n";
	private FeatureModel featureModel;

	public FeatureModelJPFBDD(final FeatureModel featureModel) {
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
		StringBuilder fields = new StringBuilder();
		for (String f : featureModel.getFeatureNames()) {
			fields.append(ANNOTATION);
			fields.append(FIELD_MODIFIER);
			fields.append(f.toLowerCase(Locale.ENGLISH));
			fields.append(";\r\n");
		}
		
		fields.append(SELECTFEATURES);
		
		for (String f : featureModel.getFeatureNames()) {
			fields.append("\t\t");
			fields.append(f.toLowerCase(Locale.ENGLISH));
			fields.append(" = Verify.getBoolean(false);\r\n");
		}
		fields.append("\t}\r\n");
		
		return fields.toString();
	}

	@Override
    public String getFormula() {
        final Node nodes = NodeCreator.createNodes(featureModel.clone()).eliminateNotSupportedSymbols(NodeWriter.javaSymbols);
        String formula = nodes.toString(NodeWriter.javaSymbols).toLowerCase(Locale.ENGLISH);
        if (formula.contains("  &&  true  &&  ! false")) {
            formula = formula.substring(0, formula.indexOf("  &&  true  &&  ! false"));
        }
        return VALID + "return " + formula + ";\r\n\t}\r\n";
    }

	@Override
    public final String getGetter() {
		return "";
	}

	@Override
    public final String getSelection() {
		StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("\t/**\r\n\t * @return The current feature-selection.\r\n\t */\r\n\tpublic static String getSelection(boolean names) {\r\n\t\t");
		ArrayList<Feature> features = new ArrayList<Feature>(featureModel.getConcreteFeatures());
		stringBuilder.append("if (names) return ");
		for (int i = 0; i < features.size(); i++) {
			if (i != 0) {
				stringBuilder.append(" + ");	
			}
			String name = features.get(i).getName();
			String lowerName = name.toLowerCase(Locale.ENGLISH);
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
