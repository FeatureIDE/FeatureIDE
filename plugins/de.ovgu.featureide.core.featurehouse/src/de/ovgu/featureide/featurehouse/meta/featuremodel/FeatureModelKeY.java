/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse.meta.featuremodel;

import java.util.Locale;

import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Defines the content of the feature model class specific for KeY.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelKeY implements IFeatureModelClass {

	private final static String HEAD = "/**\r\n * Variability encoding of the feature model for KeY.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n";
	private final static String FIELD_MODIFIER = "\tpublic static boolean ";
	
	private FeatureModel featureModel;

	public FeatureModelKeY(FeatureModel featureModel) {
		this.featureModel = featureModel;
	}
	
	@Override
	public String getImports() {
		return "";
	}

	@Override
	public String getHead() {
		return HEAD;
	}
	
	@Override
	public String getFeatureFields() {
		final StringBuilder fields = new StringBuilder();
		for (final String f : featureModel.getFeatureNames()) {
			fields.append(FIELD_MODIFIER);
			fields.append(f.toLowerCase(Locale.ENGLISH));
			fields.append(";\r\n");
		}
		return fields.toString();
	}

	@Override
	public String getFormula() {
		return "";
//		final Node nodes = NodeCreator.createNodes(featureModel.clone()).eliminateNotSupportedSymbols(NodeWriter.javaSymbols);
//		String formula = nodes.toString(NodeWriter.javaSymbols).toLowerCase(Locale.ENGLISH);
//		if (formula.contains("  &&  true  &&  ! false")) {
//			formula = formula.substring(0, formula.indexOf("  &&  true  &&  ! false"));
//		}
//		return VALID + "return " + formula + ";\r\n\t}\r\n";
	}

	@Override
	public String getGetter() {
		return "";
	}

	@Override
	public String getSelection() {
		return "";
	}

}
