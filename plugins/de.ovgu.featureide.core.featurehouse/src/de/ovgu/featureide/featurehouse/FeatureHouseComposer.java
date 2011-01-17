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
package de.ovgu.featureide.featurehouse;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;

import composer.FSTGenComposer;

import de.ovgu.cide.fstgen.ast.AbstractFSTParser;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.featurehouse.FSTParser.FSTParser;
import de.ovgu.featureide.core.featurehouse.FSTParser.JavaToken;


/**
 * Composes files using FeatureHouse.
 * 
 * @author Tom Brosch
 */
public class FeatureHouseComposer implements IComposerExtensionClass {

	public static final String JAVA_NATURE = "org.eclipse.jdt.core.javanature";
	
	private IFeatureProject featureProject = null;
	private String equation;

	public FeatureHouseComposer() {
	}

	public void initialize(IFeatureProject project) {
		featureProject = project;
	}

	public void performFullBuild(IFile equation) {
		assert(featureProject != null) : "Invalid project given";

		final String equationPath =  equation.getRawLocation().toOSString();
		final String basePath = featureProject.getSourcePath();
		final String outputPath = featureProject.getBuildPath();

		if (equationPath == null || basePath == null || outputPath == null)
			return;

		// A new FSTGenComposer instance is created every time, because this class
		// seems to remember the FST from a previous build.
		FSTGenComposer composer = new FSTGenComposer();
		//TODO output should be generated directly at outputPath not at outputPath/equation
		composer.run(new String[]{			
				"--expression", equationPath, 
				"--base-directory", basePath,
				"--output-directory", outputPath + "/", 
				"--ahead"
		});


		// ***************************************
		// TODO: Dariusz
		// Baustelle...


		FSTParser parser = new FSTParser(AbstractFSTParser.fstnodes);

		HashMap<String, List<JavaToken>> map = parser.getFileList();


		// output parsed tree
		for (String key : map.keySet()){
			List<JavaToken> list = map.get(key);
			System.out.println("=> File: " + key.toString() );
			for (JavaToken token : list)
				System.out.println("=> Token: \n" + token.toString());


		}



		TreeBuilderFeatureHouse fstparser = new TreeBuilderFeatureHouse(featureProject.getProjectName());
		fstparser.createProjectTree(composer.getFstnodes());
		featureProject.setProjectTree(fstparser.getProjectTree());
		try {
			featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	public boolean clean() {
		return true;
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
	public String replaceMarker(String text, List<String> list) {
		// no composer specific markers yet 
		return text;
	}

	@Override
	public String getEditorID(String extension) {
		if (extension == null) {
			return "";
		}
		if (extension.equals("java"))
			return "org.eclipse.jdt.ui.CompilationUnitEditor";
		if (extension.equals("cs"))
			return "";
		if (extension.equals("c"))
			return "org.eclipse.cdt.ui.editor.CEditor";
		if (extension.equals("h"))
			return "org.eclipse.cdt.ui.editor.CEditor";
		if (extension.equals("hs"))
			return "";
		if (extension.equals("jj"))
			return "";
		if (extension.equals("als"))
			return "";
		if (extension.equals("xmi"))
			return "org.eclipse.wst.xml.ui.internal.tabletree.XMLMultiPageEditorPart";
		return "";
	}

	@Override
	public boolean copyNotComposedFiles() {
		try {
			equation = featureProject.getCurrentEquationFile().getName().split("[.]")[0];
			copy(featureProject.getCurrentEquationFile());
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
		return true;
	}
	
	// copies all not composed Files of selected Features from src to bin and build
	private void copy(IFile equation) throws CoreException{
		boolean binFolderExists = false;
		if (featureProject.getBinFolder() != null)
			binFolderExists = (featureProject.getBinFolder().exists());
		ArrayList<String > selectedFeatures = getSelectedFeatures(equation);
		if (selectedFeatures != null)
			for (String feature : selectedFeatures)
				if (featureProject.getSourceFolder().getFolder(feature).exists())
					for(IResource res : featureProject.getSourceFolder().getFolder(feature).members())
						copyNotComposedFiles(null, res, binFolderExists);
	}
	
	private void copyNotComposedFiles(String folderName, IResource res, boolean binFolderExists) throws CoreException {
		boolean notComposed = true;
		for (String extension : featureProject.getComposer().extensions())
			if (res.getName().endsWith(extension))
				notComposed = false;
		if (notComposed){
			if (res instanceof IFile){
				if (folderName == null) {
					if (!featureProject.getBuildFolder().getFolder(equation).getFile(res.getName()).exists())
						res.copy(new Path (featureProject.getBuildFolder().getFolder(equation).getFullPath().toString()+"/"+res.getName()), true, null);
					if (binFolderExists)
						if (!featureProject.getBuildFolder().getFolder(equation).getFile(res.getName()).exists())
							res.copy(new Path (featureProject.getBinFolder().getFolder(equation).getFullPath().toString()+"/"+res.getName()), true, null);
				} else {
					if (!featureProject.getBuildFolder().getFolder(equation).getFolder(folderName).getFile(res.getName()).exists())
						res.copy(new Path (featureProject.getBuildFolder().getFolder(equation).getFolder(folderName).getFullPath().toString()+"/"+res.getName()), true, null);
					if (binFolderExists)
						if (!featureProject.getBuildFolder().getFolder(equation).getFolder(folderName).getFile(res.getName()).exists())
							res.copy(new Path (featureProject.getBinFolder().getFolder(equation).getFolder(folderName).getFullPath().toString()+"/"+res.getName()), true, null);
				}
			}
			if (res instanceof IFolder){
				if (folderName == null) {
					createFolder(featureProject.getBuildFolder().getName()+"/"+equation+"/"+res.getName());
					if (binFolderExists)
						createFolder(featureProject.getBinFolder().getName()+"/"+equation+"/"+res.getName());
					for (IResource res2 : ((IFolder) res).members())
						copyNotComposedFiles(res.getName(), res2, binFolderExists);
				} else {
					createFolder(featureProject.getBuildFolder().getName()+"/"+equation+"/"+folderName+"/"+res.getName());
					if (binFolderExists)
						createFolder(featureProject.getBinFolder().getName()+"/"+equation+"/"+folderName+"/"+res.getName());
					for (IResource res2 : ((IFolder) res).members())
						copyNotComposedFiles(folderName+"/"+res.getName(), res2, binFolderExists);
				}
			}
		}
		
	}


	private static ArrayList<String> getSelectedFeatures(IFile equation) {
		File equationFile = equation.getRawLocation().toFile();
		return getTokenListFromFile(equationFile);
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
			if(scanner!=null)scanner.close();
		}
		return list;
	}

	private void createFolder(String name) {
		IFolder folder = featureProject.getProject().getFolder(name);
		try {
			if (!folder.exists())
				folder.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}
	

	@Override
	public boolean postAddNature(IFolder source, IFolder destination) {
		return false;
	}

	@Override
	public void buildFSTModel() {
	}

	@Override
	public ArrayList<String[]> getTemplates(){

		ArrayList<String[]> list = new ArrayList<String[]>();

		String[] alloy = {"Alloy", "als", "module #classname#"};
		String[] c = {"C", "c", ""};
		String[] cs = {"C#", "cs", "public class #classname# {\n\n}"};
		String[] haskell= {"Haskell", "hs", "module #classname# where \n{\n\n}"};
		String[] java = {"Java", "java", "public class #classname# {\n\n}"};
		String[] javacc= {"JavaCC", "jj", "PARSER_BEGIN(#classname#) \n \n PARSER_END(#classname#)"};
		String[] uml = {"UML", "xmi", "<?xml version = '1.0' encoding = 'UTF-8' ?> \n	<XMI xmi.version = '1.2' xmlns:UML = 'org.omg.xmi.namespace.UML'>\n\n</XMI>"};

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
	public void postCompile(IFile file) {
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
				FeatureHouseCorePlugin.getDefault().logError(e);
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
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public boolean hasFeatureFolders() {

		return true;
	}


	@Override
	public int getDefaultTemplateIndex() {
	
		return 4;
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
