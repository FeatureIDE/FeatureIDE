/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.typecheck.correction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.TypecheckCorePlugin;
import de.ovgu.featureide.core.typecheck.check.CheckProblem;

/**
 * TODO description
 * 
 * @author soenke
 */
public class FIDEProblemHandler implements IProblemHandler {

    IFeatureProject project;

    TypecheckCorePlugin plugin;

    List<IFile> marked_files = new ArrayList<IFile>();

    public FIDEProblemHandler(IFeatureProject project) {
	this.project = project;
	this.plugin = TypecheckCorePlugin.getDefault();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.ovgu.featureide.core.typecheck.correction.IProblemHandler#handleProblems
     * (java.util.Collection)
     */
    @Override
    public void handleProblems(Collection<CheckProblem> problems) {
	// TypecheckCorePlugin.getDefault().clearMarkers(project.getSourceFolder());
	clearMarkers(project.getSourceFolder());
	for (CheckProblem problem : problems) {
	    createMarker(problem);
	}
    }

    public void clearMarkers(IResource res) {
	 plugin.clearMarkers(res);
//	 project.deleteBuilderMarkers(res, IResource.DEPTH_INFINITE);
//	project.deleteTypecheckMarkers(res, IResource.DEPTH_INFINITE);
    }

    // TODO: change the method from using the FIDE build markers to use own
    // markers
    protected void createMarker(CheckProblem problem) {
	IFile file = project.getSourceFolder().getFile(
		new Path(problem.getFilename()).makeRelativeTo(project
			.getSourceFolder().getRawLocation()));

	 plugin.createMarker(file, problem.getMessage(),
	 problem.getLinenumber(), problem.getSeverity());
//	 project.createBuilderMarker(file, problem.getMessage(),
//	 problem.getLinenumber(), 2);
//	project.createTypecheckMarker(file, problem.getMessage(),
//		problem.getLinenumber(), problem.getSeverity());
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.ovgu.featureide.core.typecheck.correction.IProblemHandler#log(java
     * .lang.String)
     */
    @Override
    public void log(String message) {
	// TODO Auto-generated method stub

    }

}
