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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.preprocessor.PPComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Build the FSTModel for preprocessor projects.
 * 
 * @author Jens Meinicke
 */
public class PPModelBuilder {

	protected final IFeatureProject featureProject;

	protected FSTModel model;
	protected List<String> featureNames = Collections.emptyList();
	
	public PPModelBuilder(IFeatureProject featureProject) {
		model = new FSTModel(featureProject);
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}
	
	public void buildModel() {
		model.reset();
		
		featureNames = featureProject.getFeatureModel().getConcreteFeatureNames();
		System.err.println("buildModel(): featureNames: " + featureNames);
		for (String featureName : featureNames) {
			FSTFeature fstFeature = model.addFeature(featureName);
			Feature feature = featureProject.getFeatureModel().getFeature(featureName);
			fstFeature.setColor(feature.getColorList().getColor());
		}
		try {
			buildModel(featureProject.getSourceFolder(), "");
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		featureProject.setFSTModel(model);
	}
	
	protected IFile currentFile = null;

	/**
	 * @param folder
	 * @param packageName 
	 * @throws CoreException 
	 */
	private void buildModel(IFolder folder, String packageName) throws CoreException {		
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				buildModel((IFolder)res, packageName.isEmpty() ? res.getName() : packageName + "/" + res.getName());
			} else if (res instanceof IFile) {
				currentFile = (IFile) res;
				String text = getText(currentFile);
				String className = packageName.isEmpty() ? res.getName() : packageName + "/" + res.getName();
	
				Vector<String> lines = PPComposerExtensionClass.loadStringsFromFile(currentFile);
				boolean classAdded = false;
				for (String feature : featureNames) {
					if (containsFeature(text, feature)) {
						System.err.println("buildModel2 :" + feature + " - " + className);
						model.addRole(feature, className, currentFile);
						classAdded = true;
					}
				}
				if (classAdded) {
					LinkedList<FSTDirective> directives = buildModelDirectivesForFile(lines);
					addDirectivesToModel(directives, currentFile, className);
				} else {
					// add class without annotations
					model.addClass(new FSTClass(className));
				}
			}
		}
	}

	private void addDirectivesToModel(LinkedList<FSTDirective> list, IFile res, String className) {
		for (FSTDirective d : list) {
			for (String featureName : d.getFeatureNames()) {
				FSTRole role = model.addRole(featureName, className, res);//addRole(getFeatureName(d.getExpression()), res.getName(), res);
				role.add(d);
				addDirectivesToModel(d.getChildrenList(), res, className);
			}
			
		}
	}

	protected List<String> getFeatureNames(String expression) {
		expression = expression.replaceAll("[(]", "");
		List <String> featureNameList = new LinkedList<String>();
		featureNameList.add(expression.replaceAll("[)]", "").trim());
		return featureNameList;
	}

	/**
	 * This method should be implemented by preprocessor plug-ins.
	 * Adds directives to model.
	 * 
	 * @param currentClass
	 * 			The current class.
	 * @param res
	 * 			The current file.
	 */
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return new LinkedList<FSTDirective>();
	}

	/**
	 * This method should be implemented by preprocessor plug-ins.
	 * Return true if the file contains the feature.
	 * @param text
	 * 			The file text.
	 * @param feature 
	 * 			The current feature.
	 */
	protected boolean containsFeature(String text, String feature) {
		return text.contains(feature);
	}
	
	/**
	 * @param iFile
	 */
	private String getText(IFile iFile) {
		Scanner scanner = null;
		try {
			File file = iFile.getRawLocation().toFile();
			StringBuilder fileText = new StringBuilder();
			scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append("\r\n");
			}
			return fileText.toString();
		} catch (FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally{
			if(scanner!=null)
				scanner.close();
		}
		return "";
	}

}
