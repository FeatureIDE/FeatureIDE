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
package de.ovgu.featureide.featurecpp.model;

import java.io.FileNotFoundException;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.featurecpp.FeatureCppCorePlugin;

/**
 * Builds the FSTModel for feature c++ projects
 * 
 * @author Jens Meinicke
 */
public class FeatureCppModelBuilder {
	private FSTModel model;

	private IFeatureProject featureProject;
	
	private FSTFeature currentFeature = null;
	private FSTClass currentClass = null;
	private IFile currentFile = null;

	private IFolder tempFolder;

	public FeatureCppModelBuilder(IFeatureProject featureProject, IFolder tempFolder) {
		this.tempFolder = tempFolder;
		FSTModel oldModel = featureProject.getFSTModel();
		if (oldModel != null)
			oldModel.markObsolete();

		model = new FSTModel(featureProject.getProjectName());
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}
	
	public void resetModel() {
		model.reset();
	}
	
	/**
	 * Builds The full FSTModel
	 */
	public boolean buildModel() {
		LinkedList<IFile> infoFiles = getInfoFiles();
		if (infoFiles.isEmpty()) {
			return false;
		}
		for (IFile file : infoFiles) {
			buildModel(file);
		}
		return true;
	}
	
	/**
	 * adds the informations of this class to the FSTModel
	 * @param file
	 */
	public void buildModel(IFile file) {
		LinkedList<String> infos = getInfo(file);
		String className = infos.getFirst().split("[;]")[2] + ".h";
		for (String info : infos) {
			String[] array = info.split("[;]");
			addFeature(array[0]);
			addClass(className);
			currentFeature.getClasses().put(className, currentClass);
			if (array.length == 7) {
				addField(array);
			} else {
				addMethod(array);
			}
		}
	}
	
	/**
	 * @param className
	 */
	private void addClass(String className) {
		for (String key : currentFeature.getClasses().keySet()) {
			FSTClass fstclass = currentFeature.getClasses().get(key);
			if (fstclass.getFile().equals(getFile(className))) {
				currentClass = fstclass;
				return;
			}
		}
		currentClass = new FSTClass(className);
		currentFile = getFile(className);
		currentClass.setFile(currentFile);
		model.addClass(className, currentFile);
	}
	
	private void addFeature(String feature) {
		currentFeature = model.addFeature(feature);
	}

	private void addField(String[] array) {
		FSTField field = new FSTField(array[4], array[5], 0, array[6]);
		field.setOwn(currentFile);
		currentClass.add(field);
	}

	private void addMethod(String[] array) {
		FSTMethod method = new FSTMethod(array[4], getParameter(array), array[5], array[6]);
		method.setOwn(currentFile);
		currentClass.add(method);
	}

	private LinkedList<String> getParameter(String[] array) {
		LinkedList<String> parameter = new LinkedList<String>();
		for (int i = 8;i < array.length;i++) {
			parameter.add(array[i]);
		}
		return parameter;
	}

	private IFile getFile(String className) {
		return featureProject.getSourceFolder()
			.getFolder(currentFeature.getName()).getFile(className);
	}

	private LinkedList<String> getInfo(IFile file) {
		LinkedList<String> informations = new LinkedList<String>();
		Scanner scanner = null;
		try {
			scanner = new Scanner(file.getRawLocation().toFile(), "UTF-8");
			while(scanner.hasNext()) {
				informations.add(scanner.nextLine());
			}
		} catch (FileNotFoundException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return informations;
	}

	/**
	 * @return all info files
	 */
	private LinkedList<IFile> getInfoFiles() {
		LinkedList<IFile> files = new LinkedList<IFile>();
		if (!tempFolder.exists()) {
			return files;
		}
		try {
			for (IResource res : tempFolder.members()) {
				if (res instanceof IFile) {
					if (res.getName().endsWith(".info")) {
						files.add((IFile)res);
					}
				}
			}
		} catch (CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
		return files;
	}
}
