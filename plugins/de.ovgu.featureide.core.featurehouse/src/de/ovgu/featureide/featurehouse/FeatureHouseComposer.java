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
package de.ovgu.featureide.featurehouse;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;

import cide.gparser.ParseException;

import composer.FSTGenComposer;
import composer.IParseErrorListener;

import de.ovgu.cide.fstgen.ast.AbstractFSTParser;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.featurehouse.model.FeatureHouseModelBuilder;

/**
 * Composes files using FeatureHouse.
 * 
 * @author Tom Brosch
 */
public class FeatureHouseComposer extends ComposerExtensionClass {

	private static final String SOURCE_ENTRY = "\t<classpathentry kind=\"src\" path=\"";
	private static final String EXCLUDE_ENTRY = "\t<classpathentry excluding=\"";
	private static final String EXCLUDE_SOURCE_ENTRY = "\" kind=\"src\" path=\"";

	public FeatureHouseModelBuilder fhModelBuilder;
	
	private IParseErrorListener listener = new IParseErrorListener() {
		
		@Override
		public void parseErrorOccured(ParseException arg) {
			FeatureHouseCorePlugin.getDefault().logError("FeatureHouse composer error: " + arg.getMessage(), null);
			// TODO #287 add composer errors to source files
		}
	};
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#initialize(de.ovgu.featureide.core.IFeatureProject)
	 */
	@Override
	public void initialize(IFeatureProject project) {
		super.initialize(project);
		fhModelBuilder = new FeatureHouseModelBuilder(project);
	}
	
	public void performFullBuild(IFile config) {
		assert (featureProject != null) : "Invalid project given";

		final String configPath = config.getRawLocation().toOSString();
		final String basePath = featureProject.getSourcePath();
		final String outputPath = featureProject.getBuildPath();

		if (configPath == null || basePath == null || outputPath == null)
			return;

		// A new FSTGenComposer instance is created every time, because this
		// class
		// seems to remember the FST from a previous build.
		IFolder buildFolder = featureProject.getBuildFolder().getFolder(
				config.getName().split("[.]")[0]);
		if (!buildFolder.exists()) {
			try {
				buildFolder.create(true, true, null);
			} catch (CoreException e) {
				FeatureHouseCorePlugin.getDefault().logError(e);
			}
		}

		setJaveBuildPath(config.getName().split("[.]")[0]);

		FSTGenComposer composer = new FSTGenComposer();
		composer.addParseErrorListener(listener);
		composer.run(new String[]{			
				"--expression", configPath, 
				"--base-directory", basePath,
				"--output-directory", outputPath + "/", 
				"--ahead"
		});
		
		fhModelBuilder.buildModel(AbstractFSTParser.fstnodes);

		TreeBuilderFeatureHouse fstparser = new TreeBuilderFeatureHouse(
				featureProject.getProjectName());
		fstparser.createProjectTree(composer.getFstnodes());
		featureProject.setProjectTree(fstparser.getProjectTree());
		try {
			featureProject.getProject().refreshLocal(
					IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	private void setJaveBuildPath(String buildPath) {
		Scanner scanner = null;
		FileWriter fw = null;
		IFile iClasspathFile = featureProject.getProject()
				.getFile(".classpath");
		try {
			File file = iClasspathFile.getRawLocation().toFile();
			StringBuffer fileText = new StringBuffer();
			scanner = new Scanner(file);
			while (scanner.hasNext()) {
				String line = scanner.nextLine();
				if (line.contains(SOURCE_ENTRY)) {
					fileText.append(SOURCE_ENTRY
							+ featureProject.getBuildFolder().getName() + "/"
							+ buildPath + "\"/>");
					fileText.append("\r\n");
				} else if (line.contains(EXCLUDE_ENTRY)) {
					fileText.append(line.substring(0,
							line.indexOf(EXCLUDE_SOURCE_ENTRY)
									+ EXCLUDE_SOURCE_ENTRY.length())
							+ featureProject.getBuildFolder().getName()
							+ "/"
							+ buildPath + "\"/>");
					fileText.append("\r\n");
				} else {
					fileText.append(line);
					fileText.append("\r\n");
				}
			}
			String fileTextString = fileText.toString();
			fw = new FileWriter(file);
			fw.write(fileTextString);
			iClasspathFile.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (FileNotFoundException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
			if (fw != null) {
				try {
					fw.close();
				} catch (IOException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}

			}
		}
	}

	@Override
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".java");
		extensions.add(".cs");
		extensions.add(".c");
		extensions.add(".h");
		extensions.add(".hs");
		extensions.add(".jj");
		extensions.add(".als");
		extensions.add(".xmi");
		return extensions;
	}

	@Override
	public boolean copyNotComposedFiles() {
		try {
			copy(featureProject.getCurrentConfiguration());
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
		return true;
	}

	// copies all not composed Files of selected Features from src to bin and
	// build
	private void copy(IFile config) throws CoreException {
		ArrayList<String> selectedFeatures = getSelectedFeatures(config);
		if (selectedFeatures != null)
			for (String feature : selectedFeatures) {
				IFolder folder = featureProject.getSourceFolder().getFolder(
						feature);
				copy(folder,
						featureProject.getBuildFolder().getFolder(
								config.getName().split("[.]")[0]));
			}
	}

	private void copy(IFolder featureFolder, IFolder buildFolder)
			throws CoreException {
		if (!featureFolder.exists()) {
			return;
		}

		for (IResource res : featureFolder.members()) {
			if (res instanceof IFolder) {
				IFolder folder = buildFolder.getFolder(res.getName());
				if (!folder.exists()) {
					folder.create(false, true, null);
				}
				copy((IFolder) res, folder);
			} else if (res instanceof IFile) {
				if (!res.getName().contains(".") || !extensions().contains("." + res.getName().split("[.]")[1])) {
					IFile file = buildFolder.getFile(res.getName());
					if (!file.exists()) {
						res.copy(file.getFullPath(), true, null);
					}
				}
			}
		}
	}

	private static ArrayList<String> getSelectedFeatures(IFile config) {
		File configFile = config.getRawLocation().toFile();
		return getTokenListFromFile(configFile);
	}

	private static ArrayList<String> getTokenListFromFile(File file) {
		ArrayList<String> list = null;
		Scanner scanner = null;

		try {
			scanner = new Scanner(file);

			if (scanner.hasNext()) {
				list = new ArrayList<String>();
				while (scanner.hasNext()) {
					list.add(scanner.next());
				}

			}

		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} finally {
			if (scanner != null)
				scanner.close();
		}
		return list;
	}

	@Override
	public ArrayList<String[]> getTemplates() {

		ArrayList<String[]> list = new ArrayList<String[]>();

		String[] alloy = { "Alloy", "als", "module #classname#" };
		String[] c = { "C", "c", "" };
		String[] cs = { "C#", "cs", "public class #classname# {\n\n}" };
		String[] haskell = { "Haskell", "hs",
				"module #classname# where \n{\n\n}" };
		String[] java = { "Java", "java", "public class #classname# {\n\n}" };
		String[] javacc = { "JavaCC", "jj",
				"PARSER_BEGIN(#classname#) \n \n PARSER_END(#classname#)" };
		String[] uml = {
				"UML",
				"xmi",
				"<?xml version = '1.0' encoding = 'UTF-8' ?> \n	<XMI xmi.version = '1.2' xmlns:UML = 'org.omg.xmi.namespace.UML'>\n\n</XMI>" };

		list.add(alloy);
		list.add(c);
		list.add(cs);
		list.add(haskell);
		list.add(java);
		list.add(javacc);
		list.add(uml);

		return list;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile file) {
		super.postCompile(delta, file);
		try {
			if (!file.getWorkspace().isTreeLocked()) {
				file.refreshLocal(IResource.DEPTH_ZERO, null);
			}
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public int getDefaultTemplateIndex() {
		return 4;
	}
	
	@Override
	public void buildFSTModel() {
		performFullBuild(featureProject.getCurrentConfiguration());
	}
}
