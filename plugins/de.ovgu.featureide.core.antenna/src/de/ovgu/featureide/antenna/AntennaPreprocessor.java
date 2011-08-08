/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.antenna;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;

import antenna.preprocessor.v3.PPException;
import antenna.preprocessor.v3.Preprocessor;

import de.ovgu.featureide.antenna.model.AntennaModelBuilder;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;

/**
 * Antenna: a purposely-simple Java preprocessor.
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class AntennaPreprocessor extends ComposerExtensionClass {

	private ArrayList<String> features;
	private Preprocessor preprocessor;

	private AntennaModelBuilder antennaModelBuilder;

	@Override
	public void initialize(IFeatureProject project) {
		super.initialize(project);
		antennaModelBuilder = new AntennaModelBuilder(project);
		preprocessor = new Preprocessor(new AntennaLogger(),
				new AntennaLineFilter());
		
		if (project.getProjectSourcePath() == null || project.getProjectSourcePath().equals("")) {
			project.setPaths(project.getBuildPath(), project.getBuildPath(), project.getConfigPath());
		}

		setRecursiveUnderived(project.getBuildFolder());
	}
	
	private void setRecursiveUnderived(IFolder folder) {
		try {
			for (IResource res : folder.members()) {
				res.setDerived(false, null);
				
				if (res instanceof IFolder) {
					setRecursiveUnderived((IFolder) res);
				}
			}
		} catch (CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".java");
		return extensions;
	}

	@Override
	public void performFullBuild(IFile config) {
		assert (featureProject != null) : "Invalid project given";

		final String configPath = config.getRawLocation().toOSString();

		if (configPath == null)
			return;

		// add symbol definitions
		features = readFeaturesfromConfigurationFile(config.getRawLocation()
				.toFile());
		if (features == null) {
			return;
		}

		String featureList = "";
		for (String feature : features) {
			featureList += feature + ",";
		}

		featureList = featureList.substring(0, featureList.length() - 1);

		// add source files
		try {
			preprocessor.addDefines(featureList);

			addSourceFiles(featureProject.getBuildFolder());
		} catch (CoreException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (PPException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (FileNotFoundException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AntennaCorePlugin.getDefault().logError(e);
		}

		if (antennaModelBuilder != null)
			antennaModelBuilder.buildModel();

	}
	
	/* 
	 * buildFile is not set to derived
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#postCompile(org.eclipse.core.resources.IResourceDelta, org.eclipse.core.resources.IFile)
	 */
	@Override
	public void postCompile(IResourceDelta delta, IFile buildFile) {
	}

	private void addSourceFiles(IFolder sourceFolder) throws CoreException,
			FileNotFoundException, IOException {

		for (IResource res : sourceFolder.members()) {
			if (res instanceof IFolder) {
				addSourceFiles((IFolder) res);
			} else if (res instanceof IFile) {
				Vector<String> lines = new Vector<String>();

				InputStream istr = ((IFile) res).getContents();
				Preprocessor.loadStrings(lines, istr,
						((IFile) res).getCharset());
				istr.close();
				featureProject.deleteBuilderMarkers(res, 0);
				
				boolean changed = false;
				
				try {
					changed = preprocessor.preprocess(lines,
						((IFile) res).getCharset());
				}
				catch (PPException e){
					featureProject.createBuilderMarker(res, e.getMessage().replace("Line #" + e.getLineNumber() + " :", "Antenna:"),
														e.getLineNumber()+1, IMarker.SEVERITY_ERROR);
					AntennaCorePlugin.getDefault().logError(e);
				}
				
				if (changed) {
					FileOutputStream ostr = new FileOutputStream(res
							.getRawLocation().toOSString());
					Preprocessor.saveStrings(lines, ostr,
							((IFile) res).getCharset());
					ostr.close();

					res.refreshLocal(IResource.DEPTH_ZERO, null);
				}
			}
		}
	}

	public ArrayList<String> readFeaturesfromConfigurationFile(File file) {
		Scanner scanner = null;
		try {
			ArrayList<String> list;
			scanner = new Scanner(file);
			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}
				return list;
			} else {
				return null;
			}
		} catch (FileNotFoundException e) {
			AntennaCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return null;
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		ArrayList<String[]> list = new ArrayList<String[]>();
		String[] java = { "Java", "java", "public class #classname# {\n\n}" };
		list.add(java);
		return list;
	}

	@Override
	public boolean clean() {
		return false;
	}
	
	@Override
	public boolean hasFeatureFolders() {
		return false;
	}
	
	@Override
	public boolean hasFeatureFolder() {
		return false;
	}

	@Override
	public boolean copyNotComposedFiles() {
		return true;
	}

	@Override
	public void buildFSTModel() {
		antennaModelBuilder.buildModel();
	}
}
