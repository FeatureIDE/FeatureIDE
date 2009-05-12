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
package featureide.core.builder;

import java.io.IOException;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.builder.aheadwrapper.AheadBuildErrorEvent;
import featureide.core.builder.aheadwrapper.AheadBuildErrorListener;
import featureide.core.builder.aheadwrapper.AheadWrapper;

/**
 * This is the builder class for a jak project. It implements the
 * IncrementalProjectBuilder interface. It uses the AheadWrapper
 * to build a jak project.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * @deprecated
 */
public class JakBuilder extends IncrementalProjectBuilder {

	public static final String BUILDER_ID = "DEPRECATED.jakBuilder";
	
	private JakBuilderErrorListener buildErrorListener = new JakBuilderErrorListener();

	private IFeatureProject featureProject;
	
	private AheadWrapper ahead;

	private boolean featureProjectLoaded() {
		if (featureProject != null)
			return true;

		featureProject = CorePlugin.getProjectData(getProject());
		if (featureProject == null)
			return false;
		
		initAhead();
		return true;		
	}

	private void initAhead() {
		ahead = new AheadWrapper(featureProject);
		ahead.addBuildErrorListener(buildErrorListener);
		setEquation(featureProject.getCurrentEquationFile());
	}

	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (!featureProjectLoaded())
			return;
		
		IFile equationFile = featureProject.getCurrentEquationFile();
		if (equationFile == null)
			return;
		
		String equation = equationFile.getName();
		if (equation.contains(".") ) {
			equation = equation.substring(0, equation.indexOf('.'));
		}
		
		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(), IResource.DEPTH_INFINITE);
		
		featureProject.getBinFolder().getFolder(equation).delete(true, monitor);
		featureProject.getBuildFolder().getFolder(equation).delete(true, monitor);
		
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
		featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.resources.IncrementalProjectBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	@SuppressWarnings("unchecked")
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		if (!featureProjectLoaded())
			return null;

		IFile equation = featureProject.getCurrentEquationFile();

		//TODO #28: implementation for incremental build (delete only builder markers of new builded sources)
		featureProject.deleteBuilderMarkers(getProject(), IResource.DEPTH_INFINITE);
		try {
			//TODO #28: replace by change listener, that removes derived resources when their non-derived encounter part is deleted
			clean(monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}

//		System.out.println("Build: " + featureProject.getProjectName());
		if (equation == null) {
			//featureProject.createBuilderMarker(getProject(), "No equation file found", 0, IMarker.SEVERITY_WARNING);
			return null;
		}
		
		System.out.println("Equation: " + equation.getName());
		if (kind == FULL_BUILD) {
			System.out.println("Full build");
			fullBuild(equation);
		} else {
			IResourceDelta delta = getDelta(getProject());
			if (delta == null) {
				System.out.println("Clean build");
				fullBuild(equation);
			} else {
				if (delta.findMember(equation.getProjectRelativePath()) != null) {
					System.out.println("Full build (equation has changed)");
					fullBuild(equation);
				} else {
					System.out.println("Incremental build");
					//TODO #28: rebuild classes that reference builded classes
					//incrementalBuild(delta);
					fullBuild(equation);
				}
			}
		}

		try {
			featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE,	monitor);
			featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}
		return null;
	}

	private void fullBuild(IFile equation) {
		setEquation(equation);
		ahead.buildAll();
	}

	private void setEquation(IFile equation) {
		try {
			ahead.setEquation(equation);
		} catch(IOException e) {
			featureProject.createBuilderMarker(getProject(), e.getMessage(), 0, IMarker.SEVERITY_ERROR);
		}
	}

	/**
	 * Visit all changed or added Jak files, add them to the buildlist of Ahead
	 * and call the Ahead builder.
	 * 
	 * @param  delta  delta containing added or changed Jak files
	 * @throws CoreException
	 */
//	private void incrementalBuild(IResourceDelta delta) {
//		try {
//			delta.accept(new JakDeltaVisitor());
//		} catch (CoreException e) {
//			e.printStackTrace();
//		}
//		ahead.build();
//	}

	private class JakBuilderErrorListener implements AheadBuildErrorListener {
		public void parseErrorFound(AheadBuildErrorEvent event) {
			featureProject.createBuilderMarker(event.getResource(), event
					.getMessage(), event.getLine(), IMarker.SEVERITY_ERROR);
		}
	}
	
	class JakDeltaVisitor implements IResourceDeltaVisitor {
		
		/*
		 * (non-Javadoc)
		 * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
		 */
		public boolean visit(IResourceDelta delta) throws CoreException {
			if ((delta.getKind() & (IResourceDelta.ADDED | IResourceDelta.CHANGED)) > 0) {
				IResource res = delta.getResource();
				if (res instanceof IFile && res.getName().endsWith(".jak")) {
					IFile file = (IFile) res;
					featureProject.deleteBuilderMarkers(file, IResource.DEPTH_ZERO);
					try {
						ahead.addJakfile(file);
					} catch (Exception e) {
						e.printStackTrace();
					}
				}
			}
			//return true to continue visiting children
			return true;
		}

	}
}