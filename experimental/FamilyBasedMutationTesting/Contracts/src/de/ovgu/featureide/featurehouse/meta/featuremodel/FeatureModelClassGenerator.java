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

import java.io.File;
import java.io.FileNotFoundException;

import de.ovgu.contracts.utils.Writer;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * Generates a class representing the variability encoding of the feature model.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelClassGenerator {

	private final StringBuilder stringBuilder = new StringBuilder();
	
	/**
	 * The class that defines the file content.
	 */
	private IFeatureModelClass featureModelClass;
	
	public FeatureModelClassGenerator(final File featureModelFile, final String buildPath, final String type) {
		FeatureModel featureModel = new FeatureModel();
		try {
			new XmlFeatureModelReader(featureModel).readFromFile(featureModelFile);
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedModelException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (type.equals(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML)) {
			featureModelClass = new FeatureModelJPFBDD(featureModel);
		} else if (type.equals(IFeatureProject.META_THEOREM_PROVING)) {
			featureModelClass = new FeatureModelKeY(featureModel);
		} else if (type.equals(IFeatureProject.META_MODEL_CHECKING)) {
			featureModelClass = new FeatureModelJPFCore(featureModel);
		} else {
			return;
		}	
		printModel();
		Writer.setFileContent(new File(buildPath + "\\FM\\FeatureModel.java"), stringBuilder.toString());
	}

	/**
	 * Fills the {@link StringBuilder} with the file content.
	 */
	private void printModel() {
		stringBuilder.append("package FM;\r\n\r\n");
		stringBuilder.append(featureModelClass.getImports());
		stringBuilder.append(featureModelClass.getHead());
		stringBuilder.append(featureModelClass.getFeatureFields());
		stringBuilder.append("\r\n\t");
		stringBuilder.append(featureModelClass.getFormula());
		stringBuilder.append(featureModelClass.getGetter());
		stringBuilder.append(featureModelClass.getSelection());
		stringBuilder.append("\r\n}");
	}
	
}
