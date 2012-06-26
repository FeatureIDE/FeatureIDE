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
package de.ovgu.featureide.core.typecheck.correction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.check.CheckProblem;

/**
 * TODO description
 * 
 * @author soenke
 */
public class FIDEProblemHandler implements IProblemHandler {

    IFeatureProject project;

    List<IFile> marked_files = new ArrayList<IFile>();

    public FIDEProblemHandler(IFeatureProject project) {
	this.project = project;
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
	clearMarkers(project.getSourceFolder());
	for (CheckProblem problem : problems) {
	    createMarker(problem);
	}
    }

    protected void clearMarkers(IResource res) {
	if (res instanceof IFile) {
	    project.deleteBuilderMarkers(res, IResource.DEPTH_INFINITE);
	} else if (res instanceof IFolder) {
	    try {
		for (IResource r : ((IFolder) res).members()) {
		    clearMarkers(r);
		}
	    } catch (CoreException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	    }
	}
    }

    protected void createMarker(CheckProblem problem) {
	String path = problem.getFilename().split(
		project.getSourceFolder().getFullPath().toString())[1];
	IFile file = project.getSourceFolder().getFile(path);
	project.createBuilderMarker(file, problem.toString(),
		problem.getLinenumber(), 2);
	marked_files.add(file);
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
