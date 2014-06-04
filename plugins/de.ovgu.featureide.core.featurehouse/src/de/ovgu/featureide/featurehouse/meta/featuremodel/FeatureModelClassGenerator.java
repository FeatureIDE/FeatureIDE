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

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Generates a class representing the variability encoding of the feature model.
 * 
 * @author Jens Meinicke
 */
public class FeatureModelClassGenerator {

	private StringBuilder stringBuilder = new StringBuilder();
	
	/**
	 * The class that defines the file content.
	 */
	private IFeatureModelClass featureModelClass;


	/**
	 * For test purpose only
	 * @param model
	 * @param method
	 */
	public FeatureModelClassGenerator(FeatureModel featureModel, String method) {
		if (method.equals(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML)) {
			featureModelClass = new FeatureModelJPFBDD(featureModel);
		} else if (method.equals(IFeatureProject.META_THEOREM_PROVING)) {
			featureModelClass = new FeatureModelKeY(featureModel);
		} else if (method.equals(IFeatureProject.META_MODEL_CHECKING)) {
			featureModelClass = new FeatureModelJPFCore(featureModel);
		} else {
			return;
		}
		printModel();
		System.out.println(stringBuilder.toString());
	}
	
	/**
	 * Creates the feature model class of the metaproduct with the selected mechanism.
	 * @param featureProject
	 */
	public FeatureModelClassGenerator(IFeatureProject featureProject) {
		if (featureProject.getMetaProductGeneration().equals(IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML)) {
			featureModelClass = new FeatureModelJPFBDD(featureProject.getFeatureModel());
		} else if (featureProject.getMetaProductGeneration().equals(IFeatureProject.META_THEOREM_PROVING)) {
			featureModelClass = new FeatureModelKeY(featureProject.getFeatureModel());
		} else if (featureProject.getMetaProductGeneration().equals(IFeatureProject.META_MODEL_CHECKING)) {
			featureModelClass = new FeatureModelJPFCore(featureProject.getFeatureModel());
		} else {
			return;
		}	
		printModel();
		IFolder FMFolder = featureProject.getBuildFolder().getFolder(featureProject.getCurrentConfiguration().getName().split("[.]")[0]).getFolder("FM");
		try {
			FMFolder.create(true, true, null);
			saveToFile(FMFolder.getFile("FeatureModel.java"));
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * Saves the content of the {@link StringBuilder} to the given file.
	 * @param file
	 */
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
