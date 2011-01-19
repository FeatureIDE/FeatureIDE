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
package de.ovgu.featureide.ahead.wrapper;

import jak2java.Jak2JavaWrapper;

import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourceAttributes;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * The AheadWrapper class encapsulates all functionality that has to do
 * with the ahead tool suite. It provides methods to set the current
 * equation file, to add jak files that should be recompiled due to an
 * inkremental or full build. The build methods are capable of composing
 * jak files to java files as well as reduce jak files to java files and
 * compile java files to class files.
 * 
 * The actual work is than delegated to the dedicated wrapper classes.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 */
public class AheadWrapper {

	private Jak2JavaWrapper jak2java;

	private ComposerWrapper composer;

	public AheadWrapper(IFeatureProject featureProject) {
		jak2java = new Jak2JavaWrapper();
		composer = new ComposerWrapper(featureProject);
	}

	public void setEquation(IFile equation) throws IOException {
		composer.setEquation(equation);
	}

	public void addJakfile(IFile jakfile) {
		composer.addJakfileToCompose(jakfile);
	}

	public void buildAll() {
		IFile[] jakfiles = null;
		try {
			jakfiles = composer.composeAll();
		} catch (IOException ex) {
			CorePlugin.getDefault().logError(ex);
		}
		reduceJak2Java(jakfiles);
	}

	public void build() {
		IFile[] jakfiles = null;
		jakfiles = composer.compose();
		reduceJak2Java(jakfiles);
	}

	private IFile[] reduceJak2Java(IFile[] jakFiles) {
		
		IFile[] javaFiles = new IFile[jakFiles.length];
		String filename = null;
		if (jakFiles != null)
			for (int i = 0; i < jakFiles.length; i++) {
				IFile jakFile = jakFiles[i];
				if (jakFile.exists()) {
					jak2java.reduce2Java(jakFile.getRawLocation().toFile());
	
					filename = jakFile.getName();
					filename = filename.substring(0, filename.lastIndexOf('.'));
					javaFiles[i] = ((IFolder)jakFile.getParent()).getFile(filename
							+ ".java");
					
					try {
						javaFiles[i].refreshLocal(IResource.DEPTH_ZERO, null);
						ResourceAttributes attr = javaFiles[i].getResourceAttributes();
						if (attr != null) {
							attr.setReadOnly(false);
							javaFiles[i].setResourceAttributes(attr);
						}
					} catch (CoreException e) {
						AheadCorePlugin.getDefault().logError(e);
					}
				}
			}
		return javaFiles;
	}
	
	public void addBuildErrorListener(AheadBuildErrorListener listener) {
		composer.addBuildErrorListener(listener);
	}

	public void postCompile(final IFile file) {
		final IFile jakFile = ((IFolder)file.getParent()).getFile(file.getName().replace(".java",".jak"));
		CorePlugin.getDefault();
		final IFolder buildFolder = CorePlugin.getFeatureProject(jakFile).getBuildFolder();
		if (!jakFile.exists())
			return;
		Job job = new Job("create builder problem marker") {
			@Override
			public IStatus run(IProgressMonitor monitor) {
				try {
					if (file.exists()) {
						if (jakFile.exists()) {
							IMarker[] markers = file.findMarkers(null, false, IResource.DEPTH_ZERO);
							if (markers != null) {
								for (IMarker marker : markers) {
									if (marker.exists()) {
										String content = marker.getAttribute(IMarker.MESSAGE, null);
										if (!content.contains("is a raw type") && !content.contains("generic type")) {
											AheadBuildErrorEvent buildError = new AheadBuildErrorEvent(file, marker.getAttribute(IMarker.MESSAGE).toString(), AheadBuildErrorType.JAVAC_ERROR, (Integer)marker.getAttribute(IMarker.LINE_NUMBER));
											IMarker newMarker = buildError.getResource().createMarker(CorePlugin.PLUGIN_ID + ".builderProblemMarker");
											newMarker.setAttribute(IMarker.LINE_NUMBER, buildError.getLine());
											newMarker.setAttribute(IMarker.MESSAGE, buildError.getMessage());
											newMarker.setAttribute(IMarker.SEVERITY, marker.getAttribute(IMarker.SEVERITY));
										} else {
											marker.delete();
										}
									}
								}
							}
							jakFile.delete(true, null);
						}
					}
					// Remove composed Jak files after error propagation
					deleteJakFiles(buildFolder);
				} catch (CoreException e) {
					AheadCorePlugin.getDefault().logError(e);
				}
			return Status.OK_STATUS;
			}
		};
	job.setPriority(Job.DECORATE);
	job.schedule();
	}

	protected void deleteJakFiles(IFolder folder) throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFile) {
				if (res.getName().endsWith(".jak")) {
					if (((IFolder)res.getParent()).getFile(res.getName().replace(".jak", ".java")).findMarkers(null, false, IResource.DEPTH_ZERO).length == 0) {
						res.delete(true, null);
					}
				}
			} else if (res instanceof IFolder) {
				deleteJakFiles((IFolder)res);
			}
		}
	}

}
