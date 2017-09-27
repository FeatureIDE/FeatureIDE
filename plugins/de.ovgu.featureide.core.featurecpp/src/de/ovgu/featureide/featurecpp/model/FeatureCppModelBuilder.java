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
package de.ovgu.featureide.featurecpp.model;

import java.io.FileNotFoundException;
import java.util.LinkedList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.featurecpp.FeatureCppCorePlugin;

/**
 * Builds the FSTModel for feature c++ projects
 *
 * @author Jens Meinicke
 */
public class FeatureCppModelBuilder {

	private final FSTModel model;

	private final IFeatureProject featureProject;

	private FSTRole currentRole;

	private final IFolder tempFolder;

	public FeatureCppModelBuilder(IFeatureProject featureProject, IFolder tempFolder) {
		this.tempFolder = tempFolder;
		model = new FSTModel(featureProject);
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
		final LinkedList<IFile> infoFiles = getInfoFiles();
		if (infoFiles.isEmpty()) {
			return false;
		}
		for (final IFile file : infoFiles) {
			buildModel(file);
		}
		addArbitraryFiles();
		return true;
	}

	/**
	 * adds the informations of this class to the FSTModel
	 *
	 * @param file
	 */
	private void buildModel(IFile file) {
		final LinkedList<String> infos = getInfo(file);
		final String className = infos.getFirst().split("[;]")[2] + ".h";
		for (final String info : infos) {
			final String[] array = info.split("[;]");
			final String featureName = array[0];
			final IFile classFile = featureProject.getSourceFolder().getFolder(featureName).getFile(className);
			currentRole = model.addRole(featureName, model.getAbsoluteClassName(classFile), null);
			currentRole.setFile(classFile);

			if (array.length == 7) {
				addField(array);
			} else {
				addMethod(array);
			}
		}
	}

	private void addField(String[] array) {
		currentRole.getClassFragment().add(new FSTField(array[4], array[5], array[6]));
	}

	private void addMethod(String[] array) {
		currentRole.getClassFragment().add(new FSTMethod(array[4], getParameter(array), array[5], array[6]));
	}

	private LinkedList<String> getParameter(String... array) {
		final LinkedList<String> parameter = new LinkedList<String>();
		for (int i = 8; i < array.length; i++) {
			parameter.add(array[i]);
		}
		return parameter;
	}

	private LinkedList<String> getInfo(IFile file) {
		final LinkedList<String> informations = new LinkedList<String>();
		Scanner scanner = null;
		try {
			scanner = new Scanner(file.getRawLocation().toFile(), "UTF-8");
			while (scanner.hasNext()) {
				informations.add(scanner.nextLine());
			}
		} catch (final FileNotFoundException e) {
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
		final LinkedList<IFile> files = new LinkedList<IFile>();
		if (!tempFolder.exists()) {
			return files;
		}
		try {
			for (final IResource res : tempFolder.members()) {
				if (res instanceof IFile) {
					if (res.getName().endsWith(".info")) {
						files.add((IFile) res);
					}
				}
			}
		} catch (final CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
		return files;
	}

	private void addArbitraryFiles() {
		final IFolder folder = featureProject.getSourceFolder();
		for (final FSTFeature feature : model.getFeatures()) {
			final IFolder featureFolder = folder.getFolder(feature.getName());
			addArbitraryFiles(featureFolder, feature);
		}
	}

	private void addArbitraryFiles(IFolder featureFolder, FSTFeature feature) {
		try {
			for (final IResource res : featureFolder.members()) {
				if (res instanceof IFolder) {
					addArbitraryFiles((IFolder) res, feature);
				} else if (res instanceof IFile) {
					if (!featureProject.getComposer().extensions().contains(res.getFileExtension())) {
						model.addArbitraryFile(feature.getName(), (IFile) res);
					}
				}
			}
		} catch (final CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
	}
}
