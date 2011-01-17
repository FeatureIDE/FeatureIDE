/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ahead;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.ahead.wrapper.AheadBuildErrorEvent;
import de.ovgu.featureide.ahead.wrapper.AheadBuildErrorListener;
import de.ovgu.featureide.ahead.wrapper.AheadWrapper;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;


/**
 * Composes source jak files into merged jak files.
 * 
 * @author Tom Brosch
 */
public class AheadComposer implements IComposerExtensionClass {

	public static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.ahead";

	private AheadWrapper ahead;

	private IFeatureProject featureProject = null;

	private class BuilderErrorListener implements AheadBuildErrorListener {
		public void parseErrorFound(AheadBuildErrorEvent event) {
			if (featureProject != null)
				featureProject.createBuilderMarker(event.getResource(),
						event.getMessage(), event.getLine(),
						IMarker.SEVERITY_ERROR);
		}
	}

	public AheadComposer() {
	}

	public void initialize(IFeatureProject project) {
		if (project == null) {
			return;
		}
		assert (project != null) : "Invalid project given";
		featureProject = project;
		ahead = new AheadWrapper(project);
		ahead.addBuildErrorListener(new BuilderErrorListener());
		try {
			ahead.setEquation(featureProject.getCurrentEquationFile());
		} catch (IOException e) {
			featureProject.createBuilderMarker(featureProject.getProject(),
					e.getMessage(), 0, IMarker.SEVERITY_ERROR);
		}
	}

	public void performFullBuild(IFile equation) {
		assert (ahead != null) : "Ahead instance not initialized";
		try {
			ahead.setEquation(equation);
			ahead.buildAll();
		} catch (Exception e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	public boolean clean() {
		return true;
	}

	@Override
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".jak");
		return extensions;
	}

	@Override
	public String getEditorID(String extension) {
		if (extension.equals("jak")) {
			return "de.ovgu.featureide.ui.editors.JakEditor";
		}
		return "";
	}

	@Override
	public boolean copyNotComposedFiles() {
		return false;
	}

	/**
	 * Renames all java-files into jak-files and replaces "package" by "layer"
	 */
	@Override
	public boolean postAddNature(IFolder source, IFolder destination) {
		try {
			for (IResource res : source.members()) {
				if (res instanceof IFolder) {
					performRenamings(source);
				} else {
					if (res instanceof IFile) {
						IFile file = (IFile) res;
						if (file.getName().endsWith(".java")) {
							res.move(source.getFile(file.getName()
									.replaceFirst(".java", ".jak"))
									.getFullPath(), true, null);
						}
					}
				}
			}

		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		return false;
	}

	private void performRenamings(IFolder folder) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFolder) {
				performRenamings((IFolder) res);
			} else if (res instanceof IFile) {
				IFile file = (IFile) res;
				if (file.getName().endsWith(".java")) {
					performRenamings(file);
					res.move(folder.getFile(file.getName()
							.replaceFirst(".java", ".jak"))
							.getFullPath(), true, null);
				}
			}

		}
	}

	private void performRenamings(IFile iFile) {
		try {
			File file = iFile.getRawLocation().toFile();
			String fileText = "";
			Scanner scanner = new Scanner(file);
			while (scanner.hasNext()) {
				fileText += scanner.nextLine() + "\r\n";
			}
			scanner.close();

			fileText = fileText.replaceFirst("package", "layer");
			FileWriter fw = new FileWriter(file);
			fw.write(fileText);
			fw.close();
		} catch (FileNotFoundException e) {
			AheadCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public void buildFSTModel() {
		performFullBuild(null);
	}

	@Override
	public ArrayList<String[]> getTemplates() {
		ArrayList<String[]> list = new ArrayList<String[]>();
		String[] jak = { "Jak", "jak",
				"public #refines# class #classname# {\n\n}" };
		list.add(jak);
		return list;
	}
	
	@Override
	public String replaceMarker(String text, List<String> list) {
		if (list != null && list.contains("refines"))
			text = text.replace("#refines#", "refines ");
		else
			text = text.replace("#refines#", "");
		
		return text;
	}

	@Override
	public void postCompile(IFile file) {
		if (file.getName().endsWith(".java")) {
			ahead.postCompile(file);
		}
	}

	@Override
	public void addCompiler(IProject project, String sourcePath,
			String equationPath, String buildPath) {
		addNature(project);
		addClasspathFile(project, sourcePath, equationPath, buildPath);
	}

	private void addClasspathFile(IProject project, String sourcePath,
			String equationPath, String buildPath) {
		IFile iClasspathFile = project.getFile(".classpath");
		if (!iClasspathFile.exists()) {
			String bin = "bin";
			if (sourcePath.equals(bin) || equationPath.equals(bin)
					|| buildPath.equals(bin)) {
				bin = "bin2";
			}
			if (sourcePath.equals(bin) || equationPath.equals(bin)
					|| buildPath.equals(bin)) {
				bin = "bin3";
			}
			try {
				String text = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" + 
			 				  "<classpath>\n" +  
			 				  "<classpathentry kind=\"src\" path=\"" + buildPath + "\"/>\n" + 
			 				  "<classpathentry kind=\"con\" path=\"org.eclipse.jdt.launching.JRE_CONTAINER/org.eclipse.jdt.internal.debug.ui.launcher.StandardVMType/JavaSE-1.6\"/>\n" + 
			 				  "<classpathentry kind=\"output\" path=\"" + bin + "\"/>\n" + 
			 				  "</classpath>"; 
				InputStream source = new ByteArrayInputStream(text.getBytes());
				iClasspathFile.create(source, true, null);
			} catch (CoreException e) {
				AheadCorePlugin.getDefault().logError(e);
			}

		}
	}

	private void addNature(IProject project) {
		try {
			if (!project.isAccessible() || project.hasNature(JAVA_NATURE))
				return;

			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length + 1];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			newNatures[natures.length] = JAVA_NATURE;
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean hasFeatureFolders() {

		return true;
	}


	@Override
	public int getDefaultTemplateIndex() {
	
		return 0;
	}


	@Override
	public void postModelChanged() {

	}

	@Override
	public boolean hasCustomFilename() {
	
		return false;
	}

	@Override
	public boolean hasFeatureFolder() {
		return true;
	}

}
