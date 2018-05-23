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

import java.util.Locale;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Defines the content of the feature model class specific for KeY.
 * 
 * @author Jens Meinicke
 */
class FeatureModelKeY implements IFeatureModelClass {

	private static final String HEAD = "/**\r\n * Variability encoding of the feature model for KeY.\r\n * Auto-generated class.\r\n */\r\npublic class FeatureModel {\n\n";
	private static final String FIELD_MODIFIER = "\tpublic static boolean ";
	
	private FeatureModel featureModel;

	FeatureModelKeY(final FeatureModel featureModel) {
		this.featureModel = featureModel;
	}
	
	@Override
	public String getImports() {
		return "";
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
			fields.append(";\r\n");
		}
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
		return "";
	}

}
