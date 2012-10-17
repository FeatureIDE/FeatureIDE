/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.LinkedList;
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
import de.ovgu.featureide.fm.core.Feature;

/**
 * Build the FSTModel for preprocessor projects.
 * 
 * @author Jens Meinicke
 */
public class PPModelBuilder {

	protected FSTModel model;
	private IFeatureProject featureProject;
	private LinkedList<String> featureNames = new LinkedList<String>();
	
	public PPModelBuilder(IFeatureProject featureProject) {
		FSTModel oldModel = featureProject.getFSTModel();
		if (oldModel != null)
			oldModel.markObsolete();

		model = new FSTModel(featureProject.getProjectName());
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}
	
	public void buildModel() {
		model.reset();
		
		featureNames = featureProject.getFeatureModel().getConcreteFeatureNames();
		for (String featureName : featureNames) {
			FSTFeature fstFeature = new FSTFeature(featureName);
			Feature feature = featureProject.getFeatureModel().getFeature(featureName);
			fstFeature.setColor(feature.getColorList().getColor());
			
			model.getFeaturesMap().put(featureName, fstFeature);
		}
		try {
			buildModel(featureProject.getSourceFolder(), "");
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		featureProject.setFSTModel(model);
	}

	/**
	 * @param folder
	 * @param packageName 
	 * @throws CoreException 
	 */
	private void buildModel(IFolder folder, String packageName) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				buildModel((IFolder)res,packageName.isEmpty() ? res.getName() : packageName + "/" + res.getName());
			} else if (res instanceof IFile) {
				String text = getText((IFile)res);
				String resourceName = packageName.isEmpty() ? res.getName() : packageName + "/" + res.getName();
				FSTClass currentClass = new FSTClass(resourceName);
				model.addClass(resourceName, (IFile)res);
				
				Vector<String> lines = PPComposerExtensionClass.loadStringsFromFile((IFile) res);
				
				for (String feature : featureNames) {
					if (containsFeature(text, feature)) {
						FSTFeature currentFeature = model.getFeaturesMap().get(feature);
						currentFeature.getClasses().put(resourceName, currentClass);
						buildModelDirectives(feature, currentClass, (IFile) res);
					}
				}
				
				LinkedList<FSTDirective> list = buildModelDirectivesForFile(lines);
				model.getDirectives().put(currentClass.getName(), list);
				addDirectivesToModel(list, (IFile)res);
			}
		}
	}
	
	/**
	 * @param list
	 * @param res 
	 */
	private void addDirectivesToModel(LinkedList<FSTDirective> list, IFile res) {
		for (FSTDirective d : list) {
			d.file = res;
			FSTFeature feature = model.getFeature(getFeatureName(d.expression));
			
			if (feature != null) {
				feature.directives.add(d);
				d.setColor(feature.getColor());
			}
			addDirectivesToModel(d.getChildrenList(), res);
		}
	}

	/**
	 * @param expression
	 * @return
	 */
	private String getFeatureName(String expression) {
		expression = expression.replaceAll("[(]", "");
		return expression.replaceAll("[)]", "");
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
	 * Adds directives to model.
	 * @param feature
	 * 			The current feature.
	 * @param currentClass
	 * 			The current class.
	 * @param res
	 * 			The current file.
	 */
	protected void buildModelDirectives(String feature, FSTClass currentClass, IFile res) {
		
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
