/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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

import org.eclipse.core.resources.IFile;

import composer.FSTGenComposer;

import featureide.core.IFeatureProject;
import featureide.core.builder.IComposerExtensionClass;

/**
 * 
 * TODO description
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
		
		FeatureHouseCorePlugin.getDefault().logInfo("Start composition");
		FeatureHouseCorePlugin.getDefault().logInfo("Equation: " + equationPath);
		FeatureHouseCorePlugin.getDefault().logInfo("Base folder: " + basePath);
		FeatureHouseCorePlugin.getDefault().logInfo("Output: " + outputPath);
		
		// A new FSTGenComposer instance is created every time, because this class
		// seems to remember the FST from a previous build.
		FSTGenComposer composer = new FSTGenComposer();
		composer.run(new String[]{"--expression", equationPath, "--base-directory", basePath,
				  "--output-directory", outputPath + "/", "--ahead"});
		
		TreeBuilderFeatureHouse fstparser = new TreeBuilderFeatureHouse(featureProject.getProjectName());
		fstparser.createProjectTree(composer.getFstnodes());
		featureProject.setProjectTree(fstparser.getProjectTree());
	}

	public void clean() {
	}
}
