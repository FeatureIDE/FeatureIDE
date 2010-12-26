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

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import composer.FSTGenComposer;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;


/**
 * Composes files using FeatureHouse.
 * 
 * @author Tom Brosch
 */
public class FeatureHouseComposer implements IComposerExtensionClass {

	private IFeatureProject featureProject = null;
	
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
		
		/*
		for (FSTNode node : AbstractFSTParser.fstnodes) {
			node.printFST(0);
		}
		
		*/
		TreeBuilderFeatureHouse fstparser = new TreeBuilderFeatureHouse(featureProject.getProjectName());
		fstparser.createProjectTree(composer.getFstnodes());
		featureProject.setProjectTree(fstparser.getProjectTree());
		try {
			featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	public void clean() {
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
	public String getEditorID(String extension) {
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
		return true;
	}

	@Override
	public boolean composerSpecficMove(IFolder source, IFolder destination) {
		return false;
	}

	@Override
	public void buildFSTModel() {
	}
	
	@Override
	public ArrayList<String[]> getTemplates(){

		ArrayList<String[]> list = new ArrayList<String[]>();
			
		String[] alloy = {"Alloy File", "als", "module #classname#"};
		String[] c = {"C File", "c", ""};
		String[] cs = {"C# File", "cs", "public class #classname# {\n\n}"};
		String[] haskell= {"Haskell File", "hs", "module #classname# where \n{\n\n}"};
		String[] java = {"Java File", "java", "public class #classname# {\n\n}"};
		String[] javacc= {"JavaCC File", "jj", "PARSER_BEGIN(#classname#) \n \n PARSER_END(#classname#)"};
		String[] uml = {"UML File (xmi)", "xmi", "<?xml version = '1.0' encoding = 'UTF-8' ?> \n	<XMI xmi.version = '1.2' xmlns:UML = 'org.omg.xmi.namespace.UML'>\n\n</XMI>"};
	
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
	public void addCompiler(IProject project, String sourcePath,String equationPath, String buildPath) {
	}

	@Override
	public boolean hasFeatureFolders() {
		
		return true;
	}
}
