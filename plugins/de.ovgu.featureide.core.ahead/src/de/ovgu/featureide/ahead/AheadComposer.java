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
package de.ovgu.featureide.ahead;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;

import de.ovgu.featureide.ahead.wrapper.AheadBuildErrorEvent;
import de.ovgu.featureide.ahead.wrapper.AheadBuildErrorListener;
import de.ovgu.featureide.ahead.wrapper.AheadWrapper;

import featureide.core.IFeatureProject;
import featureide.core.builder.IComposerExtensionClass;

/**
 * TODO description
 * 
 * @author Tom Brosch
 */
public class AheadComposer implements IComposerExtensionClass {
	
	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.ahead";

	private AheadWrapper ahead;
	
	private IFeatureProject featureProject = null;
	
	private class BuilderErrorListener implements AheadBuildErrorListener {
		public void parseErrorFound(AheadBuildErrorEvent event) {
			if (featureProject != null)
				featureProject.createBuilderMarker(event.getResource(), event
					.getMessage(), event.getLine(), IMarker.SEVERITY_ERROR);
		}
	}
	
	public AheadComposer() {
	}

	public void initialize(IFeatureProject project) {
		assert(project != null) : "Invalid project given";
		featureProject = project;
		ahead = new AheadWrapper(project);
		ahead.addBuildErrorListener(new BuilderErrorListener());
		try {
			ahead.setEquation(featureProject.getCurrentEquationFile());
		} catch(IOException e) {
			featureProject.createBuilderMarker(featureProject.getProject(), e.getMessage(), 0, IMarker.SEVERITY_ERROR);
		}
	}

	public void performFullBuild(IFile equation) {
		assert(ahead != null) : "Ahead instance not initialized";
		try {
			ahead.setEquation(equation);
			ahead.buildAll();
		} catch (Exception e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	public void clean() {
	}
	
}
