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
package de.ovgu.featureide.featurecpp;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.featurecpp.wrapper.FeatureCppWrapper;

/**
 * A FeatureIDE extension to compose FeatureC++ files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
public class FeatureCppComposer implements IComposerExtensionClass {

	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.featurecpp";

	private final FeatureCppWrapper featureCpp = new FeatureCppWrapper(
			(FeatureCppCorePlugin.getDefault().getBundle().getLocation() + "lib/fc++v0.7.exe")
			.substring(16));

	public void clean() {
	}

	public void initialize(IFeatureProject project) {
		assert (project != null) : "Invalid project given";
		featureCpp.initialize(project.getSourceFolder(), project
				.getBuildFolder());
	}


	public void performFullBuild(IFile equation) {
		featureCpp.compose(equation);
	}

	@Override
	public ArrayList<String> extensions() {
		ArrayList<String> extensions = new ArrayList<String>();
		extensions.add(".h");
		return extensions;
	}

	@Override
	public String getEditorID(String extension) {
		if (extension.equals("h"))
			return "org.eclipse.cdt.ui.editor.CEditor";
		return "";
	}

	@Override
	public boolean copyNotComposedFiles() {
		return false;
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
		String[] c = {"Cpp Header File", "h", ""};
		list.add(c);
		return list;
	}

	@Override
	public void postCompile(IFile file) {
	}

	@Override
	public void addCompiler(IProject project , String sourcePath,String equationPath, String buildPath) {
	}@Override
	public boolean hasFeatureFolders() {
		
		return true;
	}
}
